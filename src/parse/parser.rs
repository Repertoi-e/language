use std::{
    ops::Range,
    sync::atomic::{AtomicUsize, Ordering},
};

use bumpalo::{BumpSync, Herd};
use lazy_static::lazy_static;
use thread_local::ThreadLocal;

use super::{
    ast::{Ast, AstKind, ConstantValue},
    AstRef, AstSingleOrMultiple, AstVecOf, BinOp, StringLiteralRef, Strings, SyntaxErr,
    SyntaxErrRef, Token, TokenValue, TokensVec, UnaryOp, KEYWORDS, PARSER_ARENA, PARSER_ARENA_HERD,
};
use crate::{annotations::Level, tokenize, ArenaRef, AstOption, ExprContext};

lazy_static! {
    static ref AST_ARENA_HERD: Herd = Herd::new();
    static ref AST_ARENA: ThreadLocal<BumpSync<'static>> = ThreadLocal::new();
}

// Every Ast node gets a unique ID for debugging purposes
static AST_ID: AtomicUsize = AtomicUsize::new(0);

pub struct Parser {
    filename: Option<String>,
    source: &'static str,

    parser_arena: ArenaRef,
    ast_arena: ArenaRef,

    tokens: TokensVec, // Collected from tokenizer
    it: usize,         // Token iterator

    inside_brackets: bool, // True while parsing brackets, so we count new line characters as white space
}

macro_rules! expect {
    ($self:ident, $token:expr, $pattern:pat) => {{
        let token = $token;
        let location = loc!($self, &token);
        if matches!(token, $pattern) {
            Ok(0)
        } else {
            Err((location.clone(), $self.syntax_err().loc(location)))
        }
    }};
}

macro_rules! loc {
    ($self:ident, $token:expr) => {
        match $token {
            Some(t) => t.loc.range.clone(),
            _ => $self.source.len()..$self.source.len() + 1,
        }
    };
}

pub fn range(begin: &Range<usize>, end: &Range<usize>) -> Range<usize> {
    begin.start..end.end
}

macro_rules! token_value {
    ($pat:pat) => {
        Some(Token { value: $pat, .. })
    };
}

macro_rules! eat {
    ($self:ident, $pattern:pat) => {{
        let p = $self.peek_nth_token(0);
        match p {
            Some(Token {
                value: $pattern,
                loc: _,
            }) => {
                $self.next_token();
                p
            }
            _ => None,
        }
    }};
}

macro_rules! eat_ident {
    ($self:ident) => {{
        if let Some(t) = eat!($self, TokenValue::Identifier(_)) {
            if let TokenValue::Identifier(name) = t.value {
                Some(name)
            }
            unreachable!();
        }
        None
    }};
}

macro_rules! eat_keyword {
    ($self:ident, $keyword:expr) => {{
        if let Some(t) = eat!($self, TokenValue::Keyword(_)) {
            if let TokenValue::Keyword(keyword) = t.value {
                if keyword == KEYWORDS.$keyword {
                    Some(t)
                } else {
                    $self.it -= 1;
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }};
}

macro_rules! define_parse_binop {
    ($name:ident, $token:pat, $binop:expr) => {
        fn $name(&mut self) -> Result<Option<(BinOp, AstRef)>, SyntaxErrRef> {
            if eat!(self, $token).is_some() {
                if let Some(expr) = self.parse_bitwise_or()? {
                    return Ok(Some(($binop, expr)));
                }
            }
            Ok(None)
        }
    };
}

macro_rules! define_parse_binop_keyword {
    ($name:ident, $keyword1:expr, $keyword2:expr, $binop:expr) => {
        fn $name(&mut self) -> Result<Option<(BinOp, AstRef)>, SyntaxErrRef> {
            if eat_keyword!(self, $keyword1).is_some() {
                if eat_keyword!(self, $keyword2).is_some() {
                    if let Some(expr) = self.parse_bitwise_or()? {
                        return Ok(Some(($binop, expr)));
                    }
                }
            }
            Ok(None)
        }
    };
}

macro_rules! define_parse_binop_single_keyword {
    ($name:ident, $keyword:expr, $binop:expr) => {
        fn $name(&mut self) -> Result<Option<(BinOp, AstRef)>, SyntaxErrRef> {
            if eat_keyword!(self, $keyword).is_some() {
                if let Some(expr) = self.parse_bitwise_or()? {
                    return Ok(Some(($binop, expr)));
                }
            }
            Ok(None)
        }
    };
}

impl Parser {
    pub fn new(filename: Option<String>, input: &'static str) -> Result<Self, SyntaxErrRef> {
        Ok(Self {
            tokens: tokenize(filename.clone(), input)?,
            filename,
            source: input,
            parser_arena: PARSER_ARENA.get_or(|| PARSER_ARENA_HERD.get()),
            ast_arena: AST_ARENA.get_or(|| AST_ARENA_HERD.get()),
            it: 0,
            inside_brackets: false,
        })
    }

    //
    // Parses a series of statements
    //
    pub fn parse(&mut self) -> Result<AstRef, SyntaxErrRef> {
        let p = self.it;

        let mut statements: Vec<AstRef, _> = Vec::new_in(self.ast_arena);

        loop {
            let t = self.peek_token();
            if t.is_none() {
                break;
            } else if matches!(t, token_value!(TokenValue::NewLine)) {
                self.next_token();
                continue;
            } else if let Some(statement) = self.parse_statement()? {
                let next = self.peek_token();
                if matches!(next, token_value!(TokenValue::OpenBracket)) {
                    let mut i = self.it + 1;
                    while !matches!(
                        self.peek_nth_token(i),
                        token_value!(TokenValue::ClosedBracket)
                    ) {
                        let p = self.peek_nth_token(i);
                        if p.is_none() {
                            let start = next.unwrap().loc.range.start;
                            return Err(self
                                .syntax_err()
                                .loc_msg(start..start + 1, "bracket not closed")
                                .annotation(
                                    Level::Info,
                                    start..self.source.len(),
                                    "for this piece of code",
                                    false,
                                )
                                .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(
                                    true,
                                ));
                        }
                        i += 1;
                    }
                }
                statements.push(statement);
            } else {
                break;
            }
        }

        expect!(self, self.next_token(), None).map_err(|(_, s)| s.msg("invalid statement"))?;
        // TODO: Better error messages ^, print all possible types of statements ?

        Ok(self.new_ast(
            AstKind::Module {
                body: AstVecOf::<AstRef>(statements),
            },
            p..self.it,
        ))
    }

    fn new_ast(&mut self, kind: AstKind, token_range: Range<usize>) -> AstRef {
        self.ast_arena.alloc(Ast {
            id: AST_ID.fetch_add(1, Ordering::Relaxed),
            token_range,
            kind,
        })
    }

    /*
    # NOTE: assignment MUST precede expression, else parsing a simple assignment
    # will throw a SyntaxError.
    //
    simple_stmt[stmt_ty] (memo):
    | assignment
    | &"type" type_alias
    | e=star_expressions { _PyAST_Expr(e, EXTRA) }
    | &'return' return_stmt
    | &('import' | 'from') import_stmt
    | &'raise' raise_stmt
    | 'pass' { _PyAST_Pass(EXTRA) }
    | &'del' del_stmt
    | &'yield' yield_stmt
    | &'assert' assert_stmt
    | 'break' { _PyAST_Break(EXTRA) }
    | 'continue' { _PyAST_Continue(EXTRA) }
    | &'global' global_stmt
    | &'nonlocal' nonlocal_stmt
     */
    fn parse_simple_statement(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let ast;
        if let Some(assignment) = self.parse_assignment()? {
            ast = assignment;
        } else if eat_keyword!(self, r#type).is_some() {
            ast = self.parse_type_alias()?;
        } else if let Some(star_expressions) = self.parse_star_expressions()? {
            ast = star_expressions;
        } else {
            return Ok(None);
        }

        let range = self.token_range(ast);
        if matches!(
            self.peek_token(),
            None | token_value!(TokenValue::SemiColon)
        ) {
        } else {
            expect!(self, self.peek_token(), token_value!(TokenValue::NewLine)).map_err(
                |(_, s)| {
                    s.msg("unexpected code found after end of line of code")
                        .annotation(
                            Level::Info,
                            range.clone(),
                            "this is the valid line of code",
                            true,
                        )
                        .suggestion(
                            range.end,
                            ";",
                            "add semicolon to separate statements on the same line",
                        )
                        .suggestion(range.end, "\n", "... or end the line here")
                },
            )?;
        }
        Ok(Some(ast))
    }

    /*
    type_alias[stmt_ty]:
    | "type" n=NAME t=[type_params] '=' b=expression {
        CHECK_VERSION(stmt_ty, 12, "Type statement is",
        _PyAST_TypeAlias(CHECK(expr_ty, _PyPegen_set_expr_context(p, n, Store)), t, b, EXTRA)) }
    */
    fn parse_type_alias(&mut self) -> Result<AstRef, SyntaxErrRef> {
        let p = self.it;

        // "type" keyword already is already eaten

        if let _ = eat_ident!(self) {}

        let type_params = if let Some(type_params) = self.parse_type_params()? {
            type_params
        } else {
            return Err(self
                .syntax_err()
                .loc_msg(p..p + 1, "expected type parameters"));
        };

        expect!(self, self.next_token(), token_value!(TokenValue::Equals)).map_err(|(_, s)| {
            s.msg("expected '=' after type parameters")
                .loc_msg(p..self.it, "this is the type alias statement")
        })?;

        let expression = if let Some(expr) = self.parse_expression()? {
            expr
        } else {
            return Err(self.syntax_err().loc_msg(p..p + 1, "expected expression"));
        };

        Ok(self.new_ast(
            AstKind::TypeAlias {
                name,
                type_params,
                expression,
            },
            p..self.it,
        ))
    }

    /*
    star_atom[expr_ty]:
    | a=NAME { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=target_with_star_atom ')' { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=[star_targets_tuple_seq] ')' { _PyAST_Tuple(a, Store, EXTRA) }
    | '[' a=[star_targets_list_seq] ']' { _PyAST_List(a, Store, EXTRA) }
    */
    fn parse_star_atom(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(name) = eat_ident!(self) {
            return Ok(Some(self.new_ast(
                AstKind::Name {
                    name,
                    ctx: ExprContext::Store,
                },
                p..p + 1,
            )));
        } else if let Some(t) = eat!(self, TokenValue::OpenBracket) {
            let should_stop_brackets = !self.inside_brackets;
            self.inside_brackets = true;

            // Handle recursive brackets
            if let Some(target) = self.parse_target_with_star_atom()? {
                if eat!(self, TokenValue::ClosedBracket).is_some() {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }

                    target.token_range = p..self.it;
                    return Ok(Some(target));
                } else {
                    let target_range = range(&t.loc.range, &self.token_range(target));
                    return Err(self
                        .syntax_err()
                        .loc_msg(t.loc.range, "bracket not closed")
                        .annotation(
                            Level::Info,
                            target_range.clone(),
                            "for this statement",
                            false,
                        )
                        .suggestion(target_range.end, ")", "close the bracket")
                        .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(
                            true,
                        ));
                }
            } else {
                if should_stop_brackets {
                    self.inside_brackets = false;
                }
                self.it = p;
                return Ok(None);
            }
        }

        Ok(None)

        // TODO: tuple
        // TODO: list
    }

    /*
    target_with_star_atom[expr_ty] (memo):
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Store, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Store, EXTRA) }
    | star_atom
     */
    fn parse_target_with_star_atom(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(t_primary) = self.parse_t_primary()? {
            if eat!(self, TokenValue::Dot).is_some() {
                if let Some(name) = eat_ident!(self) {
                    return Ok(Some(self.new_ast(
                        AstKind::Attribute {
                            value: t_primary,
                            attribute: name,
                            ctx: ExprContext::Store,
                        },
                        p..self.it,
                    )));
                } else {
                    self.it = p;
                }
            } else {
                self.it = p;
            }
        }

        if let Some(atom) = self.parse_star_atom()? {
            Ok(Some(atom))
        } else {
            Ok(None)
        }

        // TODO: slices
    }

    /*
    star_target[expr_ty] (memo):
    | '*' a=(!'*' star_target) {
        _PyAST_Starred(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), Store, EXTRA) }
    | target_with_star_atom
     */
    fn parse_star_target(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        let starred = if eat!(self, TokenValue::Times).is_some() {
            true
        } else {
            false
        };

        if let Some(target) = self.parse_target_with_star_atom()? {
            if starred {
                Ok(Some(self.new_ast(
                    AstKind::Starred {
                        value: target,
                        ctx: ExprContext::Store,
                    },
                    p..self.it,
                )))
            } else {
                Ok(Some(target))
            }
        } else {
            self.it = p;
            Ok(None)
        }
    }

    /*
    # NOTE: star_targets may contain *bitwise_or, targets may not.
    star_targets[expr_ty]:
    | a=star_target !',' { a }
    | a=star_target b=(',' c=star_target { c })* [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Store, EXTRA) }
    */
    fn parse_star_targets(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let first_target;
        if let Some(target) = self.parse_star_target()? {
            first_target = target;
        } else {
            return Ok(None);
        }

        let p = self.it;

        if matches!(self.peek_token(), token_value!(TokenValue::Comma)) {
            let mut targets = Vec::<AstRef, _>::new_in(self.ast_arena);
            targets.push(first_target);

            while eat!(self, TokenValue::Comma).is_some() {
                if let Some(target) = self.parse_star_target()? {
                    targets.push(target);
                } else {
                    break;
                }
            }
            return Ok(Some(self.new_ast(
                AstKind::Tuple {
                    targets: AstSingleOrMultiple::Multiple(AstVecOf::<AstRef>(targets)),
                    ctx: ExprContext::Store,
                },
                p..self.it,
            )));
        } else {
            Ok(Some(first_target))
        }

        // TODO: tuples
    }

    /*
    simple_stmts[asdl_stmt_seq*]:
    | a=simple_stmt !';' NEWLINE { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a) } # Not needed, there for speedup
    | a[asdl_stmt_seq*]=';'.simple_stmt+ [';'] NEWLINE { a }
     */
    fn parse_simple_statements(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        let first_statement;
        if let Some(statement) = self.parse_simple_statement()? {
            first_statement = statement;
        } else {
            let p = self.it;
            if matches!(self.peek_token(), token_value!(TokenValue::SemiColon)) {
                self.next_token();
                first_statement = self.new_ast(AstKind::EmptyStatement, p..p + 1);
            } else {
                return Ok(None);
            }
        }

        if !matches!(self.peek_token(), None | token_value!(TokenValue::NewLine)) {
            let mut statements = Vec::<AstRef, _>::new_in(self.ast_arena);
            statements.push(first_statement);

            loop {
                let p = self.it;
                if eat!(self, TokenValue::SemiColon).is_some() {
                    if matches!(
                        self.peek_token(),
                        None | token_value!(TokenValue::SemiColon | TokenValue::NewLine)
                    ) {
                        statements.push(self.new_ast(AstKind::EmptyStatement, p..p + 1));
                        continue;
                    }
                }

                if let Some(statement) = self.parse_simple_statement()? {
                    statements.push(statement);

                    if !matches!(self.peek_token(), token_value!(TokenValue::SemiColon)) {
                        break;
                    }
                } else {
                    break;
                }
            }
            return Ok(Some(self.new_ast(
                AstKind::Statements {
                    statements: AstVecOf::<AstRef>(statements),
                },
                p..self.it,
            )));
        } else {
            Ok(Some(first_statement))
        }
    }

    /*
    compound_stmt[stmt_ty]:
    | &('def' | '@' | 'async') function_def
    | &'if' if_stmt
    | &('class' | '@') class_def
    | &('with' | 'async') with_stmt
    | &('for' | 'async') for_stmt
    | &'try' try_stmt
    | &'while' while_stmt
    | match_stmt */
    fn parse_compound_statement(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        // TODO:

        Ok(None)
    }

    /*
    statement[asdl_stmt_seq*]: a=compound_stmt { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a) } | a[asdl_stmt_seq*]=simple_stmts { a }
     */
    fn parse_statement(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        if let Some(t) = self.peek_token() {
            if t.loc.leading_whitespace != 0 {
                return Err(self.syntax_err()
                    .loc_msg(t.range_of_leading_white_space(), "unexpected white space, this line is not part of any block, so it shouldn't have indentation")
                );
            }
        }

        if let Some(statements) = self.parse_simple_statements()? {
            Ok(Some(statements))
        } else if let Some(compound) = self.parse_compound_statement()? {
            Ok(Some(compound))
        } else {
            Ok(None)
        }
    }

    /*
    bitwise_or[expr_ty]:
    | a=bitwise_or '|' b=bitwise_xor { _PyAST_BinOp(a, BitOr, b, EXTRA) }
    | bitwise_xor
    */
    fn parse_bitwise_or(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_bitwise_xor()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        while eat!(self, TokenValue::BitwiseOr).is_some() {
            if let Some(right) = self.parse_bitwise_xor()? {
                let prev_left_range = self.token_range(left);
                left = self.new_ast(
                    AstKind::BinOp {
                        left,
                        op: BinOp::BitOr,
                        right,
                    },
                    prev_left_range.start..self.it,
                );
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    sum[expr_ty]:
    | a=sum '+' b=term { _PyAST_BinOp(a, Add, b, EXTRA) }
    | a=sum '-' b=term { _PyAST_BinOp(a, Sub, b, EXTRA) }
    | term
    */
    fn parse_sum(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_term()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        loop {
            let p = self.it;
            if eat!(self, TokenValue::Plus).is_some() {
                if let Some(right) = self.parse_term()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::Add,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else if eat!(self, TokenValue::Minus).is_some() {
                if let Some(right) = self.parse_term()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::Sub,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    term[expr_ty]:
    | a=term '*' b=factor { _PyAST_BinOp(a, Mult, b, EXTRA) }
    | a=term '/' b=factor { _PyAST_BinOp(a, Div, b, EXTRA) }
    | a=term '//' b=factor { _PyAST_BinOp(a, FloorDiv, b, EXTRA) }
    | a=term '%' b=factor { _PyAST_BinOp(a, Mod, b, EXTRA) }
    | a=term '@' b=factor { CHECK_VERSION(expr_ty, 5, "The '@' operator is", _PyAST_BinOp(a, MatMult, b, EXTRA)) }
    | invalid_factor
    | factor
    */
    fn parse_term(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_factor()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        loop {
            let p = self.it;
            if eat!(self, TokenValue::Times).is_some() {
                if let Some(right) = self.parse_factor()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::Mult,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else if eat!(self, TokenValue::Divide).is_some() {
                if let Some(right) = self.parse_factor()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::Div,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else if eat!(self, TokenValue::DivideFloor).is_some() {
                if let Some(right) = self.parse_factor()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::FloorDiv,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else if eat!(self, TokenValue::Mod).is_some() {
                if let Some(right) = self.parse_factor()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::Mod,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else if eat!(self, TokenValue::At).is_some() {
                if let Some(right) = self.parse_factor()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::MatMult,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    factor[expr_ty] (memo):
    | '+' a=factor { _PyAST_UnaryOp(UAdd, a, EXTRA) }
    | '-' a=factor { _PyAST_UnaryOp(USub, a, EXTRA) }
    | '~' a=factor { _PyAST_UnaryOp(Invert, a, EXTRA) }
    | power
    */
    fn parse_factor(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if eat!(self, TokenValue::Plus).is_some() {
            if let Some(factor) = self.parse_factor()? {
                return Ok(Some(self.new_ast(
                    AstKind::UnaryOp {
                        op: UnaryOp::Add,
                        operand: factor,
                    },
                    p..self.it,
                )));
            } else {
                self.it = p;
            }
        } else if eat!(self, TokenValue::Minus).is_some() {
            if let Some(factor) = self.parse_factor()? {
                return Ok(Some(self.new_ast(
                    AstKind::UnaryOp {
                        op: UnaryOp::Sub,
                        operand: factor,
                    },
                    p..self.it,
                )));
            } else {
                self.it = p;
            }
        } else if eat!(self, TokenValue::BitwiseNot).is_some() {
            if let Some(factor) = self.parse_factor()? {
                return Ok(Some(self.new_ast(
                    AstKind::UnaryOp {
                        op: UnaryOp::BitNot,
                        operand: factor,
                    },
                    p..self.it,
                )));
            } else {
                self.it = p;
            }
        }

        if let Some(power) = self.parse_power()? {
            Ok(Some(power))
        } else {
            Ok(None)
        }
    }

    /*
    power[expr_ty]:
    | a=await_primary '**' b=factor { _PyAST_BinOp(a, Pow, b, EXTRA) }
    | await_primary
    */
    fn parse_power(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_await_primary()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        while eat!(self, TokenValue::Power).is_some() {
            if let Some(right) = self.parse_factor()? {
                let prev_left_range = self.token_range(left);
                left = self.new_ast(
                    AstKind::BinOp {
                        left,
                        op: BinOp::Pow,
                        right,
                    },
                    prev_left_range.start..self.it,
                );
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    Primary elements are things like "obj.something.something", "obj[something]", "obj(something)", "obj" ...

    await_primary[expr_ty] (memo):
    | 'await' a=primary { CHECK_VERSION(expr_ty, 5, "Await expressions are", _PyAST_Await(a, EXTRA)) }
    | primary*/
    fn parse_await_primary(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(_) = eat_keyword!(self, r#await) {
            if let Some(primary) = self.parse_primary()? {
                return Ok(Some(
                    self.new_ast(AstKind::Await { value: primary }, p..self.it),
                ));
            } else {
                self.it = p;
            }
        } else if let Some(primary) = self.parse_primary()? {
            return Ok(Some(primary));
        }
        Ok(None)
    }

    /*
    Primary elements are things like "obj.something.something", "obj[something]", "obj(something)", "obj" ...

    primary[expr_ty]:
    | a=primary '.' b=NAME { _PyAST_Attribute(a, b->v.Name.id, Load, EXTRA) }
    | a=primary b=genexp { _PyAST_Call(a, CHECK(asdl_expr_seq*, (asdl_expr_seq*)_PyPegen_singleton_seq(p, b)), NULL, EXTRA) }
    | a=primary '(' b=[arguments] ')' {
        _PyAST_Call(a,
                 (b) ? ((expr_ty) b)->v.Call.args : NULL,
                 (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                 EXTRA) }
    | a=primary '[' b=slices ']' { _PyAST_Subscript(a, b, Load, EXTRA) }
    | atom
    */
    fn parse_primary(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut ast;
        if let Some(atom) = self.parse_atom()? {
            // Start with an atom
            ast = atom;
        } else {
            return Ok(None);
        }

        let mut p = self.it;
        loop {
            if let Some(dot) = eat!(self, TokenValue::Dot) {
                if let Some(attr) = eat_ident!(self) {
                    let prev_ast_range = self.token_range(ast);
                    ast = self.new_ast(
                        AstKind::Attribute {
                            value: ast,
                            attribute: attr,
                            ctx: ExprContext::Load,
                        },
                        prev_ast_range.start..self.it,
                    );
                    p = self.it;
                    continue;
                } else {
                    break;
                }
            } else if let Some(bracket) = eat!(self, TokenValue::OpenSquareBracket) {
                let should_stop_brackets = !self.inside_brackets;
                self.inside_brackets = true;

                if let Some(slices) = self.parse_slices()? {
                    if eat!(self, TokenValue::ClosedSquareBracket).is_some() {
                        if should_stop_brackets {
                            self.inside_brackets = false;
                        }

                        let prev_ast_range = self.token_range(ast);
                        ast = self.new_ast(
                            AstKind::Subscript {
                                value: ast,
                                slice: slices,
                                ctx: ExprContext::Load,
                            },
                            prev_ast_range.start..self.it,
                        );
                        p = self.it;
                        continue;
                    } else {
                        let target_range = range(&bracket.loc.range, &self.token_range(slices));

                        return Err(self
                            .syntax_err()
                            .loc_msg(bracket.loc.range, "bracket not closed")
                            .annotation(
                                Level::Info,
                                target_range.clone(),
                                "for this statement",
                                false,
                            )
                            .suggestion(target_range.end, "]", "close the bracket")
                            .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(
                                true,
                            ));
                    }
                } else {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }
                    self.it = p;
                    break;
                }
            } else if let Some((pargs, kwargs)) = self.parse_arguments()? {
                let prev_ast_range = self.token_range(ast);
                ast = self.new_ast(
                    AstKind::Call {
                        func: ast,
                        args: AstOption(pargs),
                        keywords: AstOption(kwargs),
                    },
                    prev_ast_range.start..self.it,
                );
                p = self.it;
                continue;
            } else {
                break;
            }

            /*else if matches!(
                self.peek_nth_token(0),
                token_value!(TokenValue::OpenBracket)
            ) {
                let should_stop_brackets = !self.inside_brackets;
                self.inside_brackets = true;

                if let Some(arguments) = self.parse_arguments()? {
                    if eat!(self, TokenValue::ClosedBracket).is_some() {
                        if should_stop_brackets {
                            self.inside_brackets = false;
                        }

                        ast = self.new_ast(
                            AstKind::Call {
                                func: ast,
                                args: arguments,
                                keywords: arguments.keywords,
                            },
                            p..self.it,
                        );
                        p = self.it;
                        continue;
                    } else {
                        let target_range = range(
                            &self.peek_nth_token(0).unwrap().loc.range,
                            &self.token_range(arguments),
                        );
                        return Err(self
                            .syntax_err()
                            .loc_msg(
                                self.peek_nth_token(0).unwrap().loc.range,
                                "bracket not closed",
                            )
                            .annotation(
                                Level::Info,
                                target_range.clone(),
                                "for this statement",
                                false,
                            )
                            .suggestion(target_range.end, ")", "close the bracket")
                            .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(
                                true,
                            ));
                    }
                } else {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }
                    self.it = p;
                    break;
                }
            } else if matches!(
                self.peek_nth_token(0),
                token_value!(TokenValue::OpenBracket)
            ) {
                let should_stop_brackets = !self.inside_brackets;
                self.inside_brackets = true;

                if let Some(genexp) = self.parse_genexp()? {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }

                    ast = self.new_ast(
                        AstKind::Call {
                            func: ast,
                            args: AstVec(vec![genexp]),
                            keywords: AstOption::None,
                        },
                        p..self.it,
                    );
                    p = self.it;
                    continue;
                } else {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }
                    self.it = p;
                    break;
                }
            }*/
        }

        Ok(Some(ast))
    }

    /*
    bitwise_xor[expr_ty]:
    | a=bitwise_xor '^' b=bitwise_and { _PyAST_BinOp(a, BitXor, b, EXTRA) }
    | bitwise_and
    */
    fn parse_bitwise_xor(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_bitwise_and()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        while eat!(self, TokenValue::Hat).is_some() {
            if let Some(right) = self.parse_bitwise_and()? {
                let prev_left_range = self.token_range(left);
                left = self.new_ast(
                    AstKind::BinOp {
                        left,
                        op: BinOp::BitXor,
                        right,
                    },
                    prev_left_range.start..self.it,
                );
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    bitwise_and[expr_ty]:
    | a=bitwise_and '&' b=shift_expr { _PyAST_BinOp(a, BitAnd, b, EXTRA) }
    | shift_expr
    */
    fn parse_bitwise_and(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_shift_expr()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        while eat!(self, TokenValue::BitwiseAnd).is_some() {
            if let Some(right) = self.parse_shift_expr()? {
                let prev_left_range = self.token_range(left);
                left = self.new_ast(
                    AstKind::BinOp {
                        left,
                        op: BinOp::BitAnd,
                        right,
                    },
                    prev_left_range.start..self.it,
                );
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    shift_expr[expr_ty]:
    | a=shift_expr '<<' b=sum { _PyAST_BinOp(a, LShift, b, EXTRA) }
    | a=shift_expr '>>' b=sum { _PyAST_BinOp(a, RShift, b, EXTRA) }
    | invalid_arithmetic
    | sum */
    fn parse_shift_expr(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut left = match self.parse_sum()? {
            Some(expr) => expr,
            None => return Ok(None),
        };

        loop {
            let p = self.it;
            if eat!(self, TokenValue::ShiftLeft).is_some() {
                if let Some(right) = self.parse_sum()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::LeftShift,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else if eat!(self, TokenValue::ShiftRight).is_some() {
                if let Some(right) = self.parse_sum()? {
                    let prev_left_range = self.token_range(left);
                    left = self.new_ast(
                        AstKind::BinOp {
                            left,
                            op: BinOp::RightShift,
                            right,
                        },
                        prev_left_range.start..self.it,
                    );
                } else {
                    self.it = p;
                    break;
                }
            } else {
                break;
            }
        }

        Ok(Some(left))
    }

    /*
    star_expression[expr_ty] (memo):
    | '*' a=bitwise_or { _PyAST_Starred(a, Load, EXTRA) }
    | expression
    */
    fn parse_star_expression(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if eat!(self, TokenValue::Times).is_some() {
            if let Some(bitwise_or) = self.parse_bitwise_or()? {
                return Ok(Some(self.new_ast(
                    AstKind::Starred {
                        value: bitwise_or,
                        ctx: ExprContext::Load,
                    },
                    p..self.it,
                )));
            } else {
                self.it = p;
            }
        }

        if let Some(expr) = self.parse_expression()? {
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /*
    star_expressions[expr_ty]:
    | a=star_expression b=(',' c=star_expression { c })+ [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Load, EXTRA) }
    | a=star_expression ',' { _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_singleton_seq(p, a)), Load, EXTRA) }
    | star_expression
    */
    fn parse_star_expressions(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(star_expression) = self.parse_star_expression()? {
            if eat!(self, TokenValue::Comma).is_some() {
                if let Some(next) = self.parse_star_expression()? {
                    let mut expressions = Vec::<AstRef, _>::new_in(self.ast_arena);
                    expressions.push(star_expression);
                    expressions.push(next);

                    while eat!(self, TokenValue::Comma).is_some() {
                        if let Some(next) = self.parse_star_expression()? {
                            expressions.push(next);
                        } else {
                            break;
                        }
                    }

                    return Ok(Some(self.new_ast(
                        AstKind::Tuple {
                            targets: AstSingleOrMultiple::Multiple(AstVecOf::<AstRef>(expressions)),
                            ctx: ExprContext::Load,
                        },
                        p..self.it,
                    )));
                } else {
                    return Ok(Some(self.new_ast(
                        AstKind::Tuple {
                            targets: AstSingleOrMultiple::Single(star_expression),
                            ctx: ExprContext::Load,
                        },
                        p..self.it,
                    )));
                }
            }
            return Ok(Some(star_expression));
        }

        Ok(None)
    }

    fn parse_strings(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        // Consecutive strings get appended to each other

        let mut strings = Vec::<StringLiteralRef, _>::new_in(self.ast_arena);
        while let Some(next) = self.peek_token() {
            if !matches!(next.value, TokenValue::String(_)) {
                break;
            }
            if let TokenValue::String(literal) = next.value {
                strings.push(literal);
                self.next_token();
                continue;
            }
            unreachable!();
        }

        if !strings.is_empty() {
            Ok(Some(self.new_ast(
                AstKind::Constant {
                    value: ConstantValue::String(Strings(strings)),
                },
                p..self.it,
            )))
        } else {
            Ok(None)
        }
    }

    /*
    slices[expr_ty]:
    | a=slice !',' { a }
    | a[asdl_expr_seq*]=','.(slice | starred_expression)+ [','] { _PyAST_Tuple(a, Load, EXTRA) }
    */
    fn parse_slices(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        println!("--- parse_slices: {:?}", self.peek_token());

        if let Some(slice) = self.parse_slice()? {
            if eat!(self, TokenValue::Comma).is_none() {
                return Ok(Some(slice));
            }
            self.it = p;
        }

        let mut slices = Vec::<AstRef, _>::new_in(self.ast_arena);
        loop {
            if let Some(star_expr) = self.parse_star_expression()? {
                slices.push(star_expr);
            }
            if let Some(slice) = self.parse_slice()? {
                slices.push(slice);
            } else {
                break;
            }

            if eat!(self, TokenValue::Comma).is_none() {
                break;
            }
        }

        if !slices.is_empty() {
            let targets = if slices.len() == 1 {
                AstSingleOrMultiple::Single(slices.pop().unwrap())
            } else {
                AstSingleOrMultiple::Multiple(AstVecOf::<AstRef>(slices))
            };

            return Ok(Some(self.new_ast(
                AstKind::Tuple {
                    targets,
                    ctx: ExprContext::Load,
                },
                p..self.it,
            )));
        }

        Ok(None)
    }

    /*
    assignment_expression[expr_ty]:
    | a=NAME ':=' ~ b=expression {
        CHECK_VERSION(expr_ty, 8, "Assignment expressions are",
        _PyAST_NamedExpr(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), b, EXTRA)) }
    */
    fn parse_assignment_expression(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(ident) = eat_ident!(self) {
            if eat!(self, TokenValue::Walrus).is_some() {
                if let Some(expr) = self.parse_expression()? {
                    let target = self.new_ast(
                        AstKind::Name {
                            name: ident,
                            ctx: ExprContext::Store,
                        },
                        p..self.it,
                    );

                    return Ok(Some(self.new_ast(
                        AstKind::NamedExpr {
                            target: target,
                            value: expr,
                        },
                        p..self.it,
                    )));
                }
            }
            self.it = p;
        }

        Ok(None)
    }

    /*
    named_expression[expr_ty]:
    | assignment_expression
    | invalid_named_expression
    | expression !':='

    invalid_named_expression(memo):
    | a=expression ':=' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use assignment expressions with %s", _PyPegen_get_expr_name(a)) }
    | a=NAME '=' b=bitwise_or !('='|':=') {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?") }
    | !(list|tuple|genexp|'True'|'None'|'False') a=bitwise_or b='=' bitwise_or !('='|':=') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot assign to %s here. Maybe you meant '==' instead of '='?",
                                          _PyPegen_get_expr_name(a)) }
    */
    fn parse_named_expression(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p: usize = self.it;

        println!("--- parse_named_expression: {:?}", self.peek_token());

        if let Some(assignment) = self.parse_assignment_expression()? {
            return Ok(Some(assignment));
        } else if let Some(expr) = self.parse_expression()? {
            if eat!(self, TokenValue::Walrus).is_none() {
                return Ok(Some(expr));
            } else {
                if let Some(_) = self.parse_expression()? {
                    return Err(self
                        .syntax_err()
                        .loc_msg(p..self.it, "cannot use assignment expression here")
                        .annotation(
                            Level::Info,
                            expr.token_range.clone(),
                            "for this statement",
                            true,
                        ));
                }
            }
            self.it = p;
        }

        Ok(None)

        // TODO: Helpful errors
    }

    /*
    arguments[expr_ty]:
      | a='(' args [','] &')' { a }
      | invalid_arguments
     */
    fn parse_arguments(
        &mut self,
    ) -> Result<Option<(Option<AstRef>, Option<AstRef>)>, SyntaxErrRef> {
        if let Some(begin_bracket) = eat!(self, TokenValue::OpenBracket) {
            let should_stop_brackets = !self.inside_brackets;
            self.inside_brackets = true;

            let (pargs, kwargs) = self.parse_args()?;
            if eat!(self, TokenValue::Comma).is_some() {
                // Optional trailing comma
            }

            if let Some(_) = eat!(self, TokenValue::ClosedBracket) {
                if should_stop_brackets {
                    self.inside_brackets = false;
                }
                return Ok(Some((pargs, kwargs)));
            } else {
                if let Some(comma) = eat!(self, TokenValue::Comma) {
                    let (pargs2, kwargs2) = self.parse_args()?;
                    if pargs2.is_some() {
                        // return error: positional argument follows keyword argument
                        // suggestion: move the arguments pargs2 with the initial ones pargs1
                        // suggestion: continue keyword arguments by naming pargs2

                        let pargs2_str = if pargs2.is_some() {
                            self.source
                                .get(self.token_range(pargs2.as_ref().unwrap()))
                                .unwrap()
                        } else {
                            ""
                        };

                        let mut named_suggestions = Vec::<String, _>::new_in(self.ast_arena);
                        if pargs2.is_some() {
                            match &pargs2.as_ref().unwrap().kind {
                                AstKind::Tuple { targets, .. } => match targets {
                                    AstSingleOrMultiple::Single(target) => {
                                        named_suggestions.push(format!(
                                            "... = {}",
                                            self.source.get(self.token_range(target)).unwrap()
                                        ));
                                    }
                                    AstSingleOrMultiple::Multiple(targets) => {
                                        for target in targets.0.iter() {
                                            named_suggestions.push(format!(
                                                "... = {}",
                                                self.source.get(self.token_range(target)).unwrap()
                                            ));
                                        }
                                    }
                                },
                                _ => unreachable!(),
                            };
                        }

                        let kwargs1_str = if kwargs.is_some() {
                            self.source
                                .get(self.token_range(kwargs.as_ref().unwrap()))
                                .unwrap()
                        } else {
                            ""
                        };

                        let kwargs2_str = if kwargs2.is_some() {
                            self.source
                                .get(self.token_range(kwargs2.as_ref().unwrap()))
                                .unwrap()
                        } else {
                            ""
                        };

                        let suggestion_move_together_str = self.parser_arena.alloc_str(&format!(
                            "{}{}{}, ...)\n",
                            pargs2_str, kwargs1_str, kwargs2_str
                        ));
                        let named_suggestions_str = self.parser_arena.alloc_str(&format!(
                            "{}{}{}, ...)\n",
                            kwargs1_str,
                            &named_suggestions.join(", "),
                            kwargs2_str
                        ));

                        return Err(self
                            .syntax_err()
                            .loc_msg(pargs2.unwrap().token_range.clone(), "positional arguments after named arguments have unclear order in which to be passed in")
                            .suggestion(comma.loc.range.end, suggestion_move_together_str, "move the positional arguments together")
                            .suggestion(comma.loc.range.end, named_suggestions_str, "... or name all the positional arguments")
                        );
                    } else if kwargs.is_some() {
                        unreachable!();
                    }
                }

                // print parsed args range
                let args_range =
                    begin_bracket.loc.range.end..self.token_range(pargs.as_ref().unwrap()).end;

                println!("--- args range: {:?}, self.it: {}", args_range, self.it);

                let in_interactive_interpreter_should_it_read_more_lines_for_anticipation_of_closing_bracket =
                    matches!(self.peek_token(), None | token_value!(TokenValue::NewLine));

                return Err(self
                    .syntax_err()
                    .loc_msg(begin_bracket.loc.range.clone(), "bracket not closed")
                    .annotation(
                        Level::Info,
                        args_range,
                        "for these arguments",
                        false,
                    )
                    .suggestion(self.it, ")", "close the bracket")
                    .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(in_interactive_interpreter_should_it_read_more_lines_for_anticipation_of_closing_bracket)
                );
            }

            /*  invalid_arguments:
               | ((','.(starred_expression | ( assignment_expression | expression !':=') !'=')+ ',' kwargs) | kwargs) a=',' ','.(starred_expression !'=')+ {
                   RAISE_SYNTAX_ERROR_STARTING_FROM(a, "iterable argument unpacking follows keyword argument unpacking") }
               | a=expression b=for_if_clauses ',' [args | expression for_if_clauses] {
                   RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, _PyPegen_get_last_comprehension_item(PyPegen_last_item(b, comprehension_ty)), "Generator expression must be parenthesized") }
               | a=NAME b='=' expression for_if_clauses {
                   RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?")}
               | (args ',')? a=NAME b='=' &(',' | ')') {
                   RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "expected argument value expression")}
               | a=args b=for_if_clauses { _PyPegen_nonparen_genexp_in_call(p, a, b) }
               | args ',' a=expression b=for_if_clauses {
                   RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, _PyPegen_get_last_comprehension_item(PyPegen_last_item(b, comprehension_ty)), "Generator expression must be parenthesized") }
               | a=args ',' args { _PyPegen_arguments_parsing_error(p, a) }
            */
        }

        Ok(None)
    }

    // args[expr_ty]:
    //   | a= (starred_expression | assignment_expression | expression )+ (separated by ',') [, kwargs]
    //   | kwargs
    fn parse_args(&mut self) -> Result<(Option<AstRef>, Option<AstRef>), SyntaxErrRef> {
        // Returns a tuple of (positional_args, keyword_args)

        let mut items = Vec::<AstRef, _>::new_in(self.ast_arena);
        loop {
            if let Some(item) = self.parse_starred_expression()? {
                items.push(item);
            } else if let Some(item) = self.parse_assignment_expression()? {
                items.push(item);
            } else if let Some(item) = self.parse_expression()? {
                items.push(item);
            } else {
                break;
            }

            if eat!(self, TokenValue::Comma).is_none() {
                break;
            }
        }

        if !items.is_empty() {
            let range = items[0].token_range.start..items.last().unwrap().token_range.end;
            let targets = if items.len() == 1 {
                AstSingleOrMultiple::Single(items.pop().unwrap())
            } else {
                AstSingleOrMultiple::Multiple(AstVecOf::<AstRef>(items))
            };
            let pargs = Some(self.new_ast(
                AstKind::Tuple {
                    targets,
                    ctx: ExprContext::Load,
                },
                range,
            ));

            if let Some(kw) = self.parse_kwargs()? {
                return Ok((pargs, Some(kw)));
            }
            return Ok((pargs, None));
        } else {
            if let Some(kw) = self.parse_kwargs()? {
                return Ok((None, Some(kw)));
            } else {
                return Ok((None, None));
            }
        }
    }

    // kwargs[asdl_seq*]:
    //   | a=','.kwarg_or_starred+ ',' b=','.kwarg_or_double_starred+
    //   | ','.kwarg_or_starred+
    //   | ','.kwarg_or_double_starred+
    fn parse_kwargs(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        let mut items = Vec::<AstRef, _>::new_in(self.ast_arena);
        loop {
            if let Some(item) = self.parse_kwarg_or_starred_or_double_starred()? {
                items.push(item);
            } else {
                break;
            }

            if eat!(self, TokenValue::Comma).is_none() {
                break;
            }
        }

        if !items.is_empty() {
            let range = items[0].token_range.start..items.last().unwrap().token_range.end;
            let targets = if items.len() == 1 {
                AstSingleOrMultiple::Single(items.pop().unwrap())
            } else {
                AstSingleOrMultiple::Multiple(AstVecOf(items))
            };

            return Ok(Some(self.new_ast(
                AstKind::Tuple {
                    targets: targets,
                    ctx: ExprContext::Load,
                },
                range,
            )));
        }
        self.it = p;
        Ok(None)
    }

    // starred_expression[expr_ty]:
    //   | invalid_starred_expression_unpacking
    //   | '*' a=expression
    //   | invalid_starred_expression
    fn parse_starred_expression(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;
        if eat!(self, TokenValue::Times).is_some() {
            if let Some(expr) = self.parse_expression()? {
                return Ok(Some(self.new_ast(
                    AstKind::Starred {
                        value: expr,
                        ctx: ExprContext::Load,
                    },
                    p..self.it,
                )));
            } else {
                self.it = p;
            }
        }
        Ok(None)
    }

    // kwarg_or_starred[KeywordOrStarred*]:
    //   | invalid_kwarg
    //   | NAME '=' expression
    //   | starred_expression
    //
    // kwarg_or_double_starred[KeywordOrStarred*]:
    //   | invalid_kwarg
    //   | NAME '=' expression
    //   | '**' expression
    fn parse_kwarg_or_starred_or_double_starred(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;
        if let Some(name) = eat_ident!(self) {
            if eat!(self, TokenValue::Equal).is_some() {
                if let Some(expr) = self.parse_expression()? {
                    return Ok(Some(self.new_ast(
                        AstKind::KeywordArg {
                            arg: name,
                            value: expr,
                            ctx: ExprContext::Load,
                        },
                        p..self.it,
                    )));
                }
            }
            self.it = p;
        } else if eat!(self, TokenValue::Power).is_some() {
            if let Some(expr) = self.parse_expression()? {
                return Ok(Some(self.new_ast(
                    AstKind::DoubleStarred {
                        value: expr,
                        ctx: ExprContext::Load,
                    },
                    p..self.it,
                )));
            }
            self.it = p;
        } else if let Some(star) = self.parse_starred_expression()? {
            return Ok(Some(self.new_ast(
                AstKind::Starred {
                    value: star,
                    ctx: ExprContext::Load,
                },
                p..self.it,
            )));
        }

        /*
        invalid_kwarg:
        | a[Token*]=('True'|'False'|'None') b='=' {
            RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to %s", PyBytes_AS_STRING(a->bytes)) }
        | a=NAME b='=' expression for_if_clauses {
            RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?")}
        | !(NAME '=') a=expression b='=' {
            RAISE_SYNTAX_ERROR_KNOWN_RANGE(
                a, b, "expression cannot contain assignment, perhaps you meant \"==\"?") }
        | a='**' expression '=' b=expression {
            RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to keyword argument unpacking") }
         */

        Ok(None)
    }

    /*
     expression[expr_ty] (memo):
     | invalid_expression
     | invalid_legacy_expression
     | a=disjunction 'if' b=disjunction 'else' c=expression { _PyAST_IfExp(b, a, c, EXTRA) }
     | disjunction
     | lambdef

     invalid_expression:
     # !(NAME STRING) is not matched so we don't show this error with some invalid string prefixes like: kf"dsfsdf"
     # Soft keywords need to also be ignored because they can be parsed as NAME NAME
    | !(NAME STRING | SOFT_KEYWORD) a=disjunction b=expression_without_invalid {
         _PyPegen_check_legacy_stmt(p, a) ? NULL : p->tokens[p->mark-1]->level == 0 ? NULL :
         RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Perhaps you forgot a comma?") }
    | a=disjunction 'if' b=disjunction !('else'|':') { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "expected 'else' after 'if' expression") }
    | a='lambda' [lambda_params] b=':' &FSTRING_MIDDLE  {
         RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "f-string: lambda expressions are not allowed without parentheses") }

     invalid_legacy_expression:
     | a=NAME !'(' b=star_expressions {
         _PyPegen_check_legacy_stmt(p, a) ? RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b,
             "Missing parentheses in call to '%U'. Did you mean %U(...)?", a->v.Name.id, a->v.Name.id) : NULL}
     */
    fn parse_expression(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(disjunction) = self.parse_disjunction()? {
            if eat_keyword!(self, r#if).is_some() {
                if let Some(disjunction2) = self.parse_disjunction()? {
                    if eat_keyword!(self, r#else).is_some() {
                        if let Some(expr) = self.parse_expression()? {
                            return Ok(Some(self.new_ast(
                                AstKind::IfExp {
                                    test: disjunction2,
                                    body: disjunction,
                                    orelse: expr,
                                },
                                p..self.it,
                            )));
                        }
                    }
                }
                self.it = p;
            }
            return Ok(Some(disjunction));
        } /*else if let Some(lambdef) = self.parse_lambdef()? {
              Ok(Some(lambdef))
          }*/

        // TODO: Helpful errors

        Ok(None)
    }

    /*
    slice[expr_ty]:
    | a=[expression] ':' b=[expression] c=[':' d=[expression] { d }] { _PyAST_Slice(a, b, c, EXTRA) }
    | a=named_expression { a }
    */
    fn parse_slice(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(expr) = self.parse_expression()? {
            if eat!(self, TokenValue::Colon).is_some() {
                if let Some(expr2) = self.parse_expression()? {
                    if eat!(self, TokenValue::Colon).is_some() {
                        if let Some(expr3) = self.parse_expression()? {
                            return Ok(Some(self.new_ast(
                                AstKind::Slice {
                                    lower: expr,
                                    upper: expr2,
                                    step: AstOption(Some(expr3)),
                                },
                                p..self.it,
                            )));
                        } else {
                            self.it = p;
                        }
                    } else {
                        return Ok(Some(self.new_ast(
                            AstKind::Slice {
                                lower: expr,
                                upper: expr2,
                                step: AstOption(None),
                            },
                            p..self.it,
                        )));
                    }
                } else {
                    self.it = p;
                }
            } else {
                return Ok(Some(expr));
            }
        } else if let Some(named_expr) = self.parse_named_expression()? {
            return Ok(Some(named_expr));
        }

        Ok(None)
    }

    /*
    disjunction[expr_ty] (memo):
    | a=conjunction b=('or' c=conjunction { c })+ { _PyAST_BoolOp(
        Or,
        CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)),
        EXTRA) }
    | conjunction
    */
    fn parse_disjunction(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        let mut conjunctions = Vec::<AstRef, _>::new_in(self.ast_arena);
        loop {
            if let Some(conjunction) = self.parse_conjunction()? {
                conjunctions.push(conjunction);
            } else {
                break;
            }

            if eat_keyword!(self, or).is_none() {
                break;
            }
        }

        if !conjunctions.is_empty() {
            if conjunctions.len() > 1 {
                return Ok(Some(self.new_ast(
                    AstKind::BoolOp {
                        op: BinOp::Or,
                        values: AstVecOf::<AstRef>(conjunctions),
                    },
                    p..self.it,
                )));
            } else {
                return Ok(Some(conjunctions.pop().unwrap()));
            }
        }

        self.it = p;
        Ok(None)
    }

    /*
    conjunction[expr_ty] (memo):
    | a=inversion b=('and' c=inversion { c })+ { _PyAST_BoolOp(
        And,
        CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)),
        EXTRA) }
    | inversion
    */
    fn parse_conjunction(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        let mut inversions = Vec::<AstRef, _>::new_in(self.ast_arena);
        loop {
            if let Some(inversion) = self.parse_inversion()? {
                inversions.push(inversion);
            } else {
                break;
            }

            if eat_keyword!(self, and).is_none() {
                break;
            }
        }

        if !inversions.is_empty() {
            if inversions.len() > 1 {
                return Ok(Some(self.new_ast(
                    AstKind::BoolOp {
                        op: BinOp::And,
                        values: AstVecOf::<AstRef>(inversions),
                    },
                    p..self.it,
                )));
            } else {
                return Ok(Some(inversions.pop().unwrap()));
            }
        }

        self.it = p;
        Ok(None)
    }

    /*
    inversion[expr_ty] (memo):
    | 'not' a=inversion { _PyAST_UnaryOp(Not, a, EXTRA) }
    | comparison
    */
    fn parse_inversion(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if eat_keyword!(self, not).is_some() {
            if let Some(inversion) = self.parse_inversion()? {
                return Ok(Some(self.new_ast(
                    AstKind::UnaryOp {
                        op: UnaryOp::Not,
                        operand: inversion,
                    },
                    p..self.it,
                )));
            }
            self.it = p;
        }
        self.parse_comparison()
    }

    /*
    comparison[expr_ty]:
    | a=bitwise_or b=compare_op_bitwise_or_pair+ {
        _PyAST_Compare(
            a,
            CHECK(asdl_int_seq*, _PyPegen_get_cmpops(p, b)),
            CHECK(asdl_expr_seq*, _PyPegen_get_exprs(p, b)),
            EXTRA) }
    | bitwise_or
    */
    fn parse_comparison(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(bitwise_or) = self.parse_bitwise_or()? {
            let mut ops = Vec::new_in(self.ast_arena);
            let mut exprs = Vec::new_in(self.ast_arena);

            while let Some((op, expr)) = self.parse_compare_op_bitwise_or_pair()? {
                ops.push(op);
                exprs.push(expr);
            }

            if !ops.is_empty() {
                return Ok(Some(self.new_ast(
                    AstKind::Compare {
                        left: bitwise_or,
                        ops: AstVecOf::<BinOp>(ops),
                        comparators: AstVecOf::<AstRef>(exprs),
                    },
                    p..self.it,
                )));
            }
            return Ok(Some(bitwise_or));
        }

        Ok(None)
    }

    /*
    compare_op_bitwise_or_pair[CmpopExprPair*]:
        | eq_bitwise_or
        | noteq_bitwise_or
        | lte_bitwise_or
        | lt_bitwise_or
        | gte_bitwise_or
        | gt_bitwise_or
        | notin_bitwise_or
        | in_bitwise_or
        | isnot_bitwise_or
        | is_bitwise_or
    */
    fn parse_compare_op_bitwise_or_pair(
        &mut self,
    ) -> Result<Option<(BinOp, AstRef)>, SyntaxErrRef> {
        if let Some(pair) = self.parse_eq_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_noteq_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_lte_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_lt_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_gte_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_gt_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_notin_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_in_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_isnot_bitwise_or()? {
            return Ok(Some(pair));
        } else if let Some(pair) = self.parse_is_bitwise_or()? {
            return Ok(Some(pair));
        }
        Ok(None)
    }

    define_parse_binop!(parse_eq_bitwise_or, TokenValue::EqualEqual, BinOp::Eq);
    define_parse_binop!(parse_noteq_bitwise_or, TokenValue::NotEqual, BinOp::NotEq);
    define_parse_binop!(
        parse_lte_bitwise_or,
        TokenValue::LessOrEqual,
        BinOp::LessOrEqual
    );
    define_parse_binop!(parse_lt_bitwise_or, TokenValue::Less, BinOp::Less);
    define_parse_binop!(
        parse_gte_bitwise_or,
        TokenValue::GreaterOrEqual,
        BinOp::GreaterOrEqual
    );
    define_parse_binop!(parse_gt_bitwise_or, TokenValue::Greater, BinOp::Greater);
    define_parse_binop_keyword!(
        parse_notin_bitwise_or,
        KEYWORDS.not,
        KEYWORDS.r#in,
        BinOp::NotIn
    );
    define_parse_binop_single_keyword!(parse_in_bitwise_or, KEYWORDS.r#in, BinOp::In);
    define_parse_binop_keyword!(
        parse_isnot_bitwise_or,
        KEYWORDS.is,
        KEYWORDS.not,
        BinOp::IsNot
    );
    define_parse_binop_single_keyword!(parse_is_bitwise_or, KEYWORDS.is, BinOp::Is);

    /*
    atom[expr_ty]:
    | NAME
    | 'True' { _PyAST_Constant(Py_True, NULL, EXTRA) }
    | 'False' { _PyAST_Constant(Py_False, NULL, EXTRA) }
    | 'None' { _PyAST_Constant(Py_None, NULL, EXTRA) }
    | &(STRING|FSTRING_START) strings
    | NUMBER
    | &'(' (tuple | group | genexp)
    | &'[' (list | listcomp)
    | &'{' (dict | set | dictcomp | setcomp)
    | '...' { _PyAST_Constant(Py_Ellipsis, NULL, EXTRA) }
    */
    fn parse_atom(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(t) = eat!(self, TokenValue::Number(_)) {
            if let TokenValue::Number(literal) = t.value {
                return Ok(Some(self.new_ast(
                    AstKind::Constant {
                        value: ConstantValue::Number(literal),
                    },
                    p..p + 1,
                )));
            }
            unreachable!();
        }

        if let Some(name) = eat_ident!(self) {
            return Ok(Some(self.new_ast(
                AstKind::Name {
                    name,
                    ctx: ExprContext::Load,
                },
                p..p + 1,
            )));
        }

        if let Some(_) = eat_keyword!(self, True) {
            return Ok(Some(self.new_ast(
                AstKind::Constant {
                    value: ConstantValue::Bool(true),
                },
                p..p + 1,
            )));
        } else if let Some(_) = eat_keyword!(self, False) {
            return Ok(Some(self.new_ast(
                AstKind::Constant {
                    value: ConstantValue::Bool(false),
                },
                p..p + 1,
            )));
        } else if let Some(_) = eat_keyword!(self, None) {
            return Ok(Some(self.new_ast(
                AstKind::Constant {
                    value: ConstantValue::None,
                },
                p..p + 1,
            )));
        }

        if let Some(strings) = self.parse_strings()? {
            return Ok(Some(strings));
        }

        // TODO     | &'(' (tuple | group | genexp)
        // | &'[' (list | listcomp)
        // | &'{' (dict | set | dictcomp | setcomp)
        // | '...' { _PyAST_Constant(Py_Ellipsis, NULL, EXTRA) }

        Ok(None)
    }

    /*
    t_primary[expr_ty]:
    | a=t_primary '.' b=NAME &t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Load, EXTRA) }
    | a=t_primary '[' b=slices ']' &t_lookahead { _PyAST_Subscript(a, b, Load, EXTRA) }
    | a=t_primary b=genexp &t_lookahead {
        _PyAST_Call(a, CHECK(asdl_expr_seq*, (asdl_expr_seq*)_PyPegen_singleton_seq(p, b)), NULL, EXTRA) }
    | a=t_primary '(' b=[arguments] ')' &t_lookahead {
        _PyAST_Call(a,
                 (b) ? ((expr_ty) b)->v.Call.args : NULL,
                 (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                 EXTRA) }
    | a=atom &t_lookahead { a }
    */
    fn parse_t_primary(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let mut ast;
        if let Some(atom) = self.parse_atom()? {
            // Start with an atom
            ast = atom;
        } else {
            return Ok(None);
        }

        let mut p = self.it;
        while matches!(self.peek_nth_token(0), token_value!(TokenValue::Dot)) {
            if matches!(
                self.peek_nth_token(1),
                token_value!(TokenValue::Identifier(_))
            ) {
                if matches!(self.peek_nth_token(2), token_value!(TokenValue::Dot)) {
                    if let TokenValue::Identifier(attr) = self.peek_nth_token(1).unwrap().value {
                        self.next_token();
                        self.next_token();

                        let prev_ast_range = self.token_range(ast);
                        ast = self.new_ast(
                            AstKind::Attribute {
                                value: ast,
                                attribute: attr,
                                ctx: ExprContext::Load,
                            },
                            prev_ast_range.start..self.it,
                        );
                        p = self.it;
                        continue;
                    }
                    unreachable!();
                } else {
                    break;
                }
            } else {
                break;

                // TODO: Update this else with more lookahead tokens, since its not gonna be the only case
                /*
                let loc_p = loc!(self, lookahead);
                return Err(self.syntax_err()
                    .loc_msg(loc_p.clone(), "stray dot detected")
                    .annotation(Level::Info, left_expr, "trying to access into this expression")
                    .suggestion(loc_p.start, "<ident>", "if you meant to access into the expression, use an identifier after the dot")
                );*/
            }
        }

        // TODO: slices
        // TODO: genexp
        // TODO: arguments

        Ok(Some(ast))
    }

    /*
    single_subscript_attribute_target[expr_ty]:
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Store, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Store, EXTRA) }
     */
    fn parse_single_subscript_attribute_target(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;
        if let Some(t_primary) = self.parse_t_primary()? {
            if eat!(self, TokenValue::Dot).is_some() {
                if let Some(ident) = eat!(self, TokenValue::Identifier(_)) {
                    if let TokenValue::Identifier(name) = ident.value {
                        return Ok(Some(self.new_ast(
                            AstKind::Attribute {
                                value: t_primary,
                                attribute: name,
                                ctx: ExprContext::Store,
                            },
                            p..self.it,
                        )));
                    }
                    unreachable!()
                } else {
                    self.it = p;
                }
            } else {
                self.it = p;
            }
        }

        // TODO slices

        Ok(None)
    }

    fn token_range(&mut self, ast: &Ast) -> Range<usize> {
        let start = &self.tokens[ast.token_range.start].loc.range;
        let end = &self.tokens[ast.token_range.end - 1].loc.range;
        range(start, end)
    }

    /*
    single_target[expr_ty]:
    | single_subscript_attribute_target
    | a=NAME { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=single_target ')' { a }
     */
    fn parse_single_target(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        if let Some(target) = self.parse_single_subscript_attribute_target()? {
            Ok(Some(target))
        } else if let Some(t) = eat!(self, TokenValue::Identifier(_)) {
            if let TokenValue::Identifier(name) = t.value {
                return Ok(Some(self.new_ast(
                    AstKind::Name {
                        name,
                        ctx: ExprContext::Store,
                    },
                    p..p + 1,
                )));
            }
            unreachable!();
        } else if let Some(t) = eat!(self, TokenValue::OpenBracket) {
            let should_stop_brackets = !self.inside_brackets;
            self.inside_brackets = true;

            // Handle recursive brackets
            if let Some(single_target) = self.parse_single_target()? {
                if eat!(self, TokenValue::ClosedBracket).is_some() {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }

                    single_target.token_range = p..self.it;
                    Ok(Some(single_target))
                } else {
                    let target_range = range(&t.loc.range, &self.token_range(single_target));
                    Err(self
                        .syntax_err()
                        .loc_msg(t.loc.range, "bracket not closed")
                        .annotation(
                            Level::Info,
                            target_range.clone(),
                            "for this statement",
                            false,
                        )
                        .suggestion(target_range.end, ")", "close the bracket")
                        .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(
                            true,
                        ))
                }
            } else {
                if should_stop_brackets {
                    self.inside_brackets = false;
                }
                self.it = p;
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    /*
    annotated_rhs[expr_ty]: yield_expr | star_expressions
     */
    fn parse_annotated_rhs(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        // yield_expr or star_expressions
        self.parse_star_expressions()
    }

    /*
    # NOTE: annotated_rhs may start with 'yield'; yield_expr must start with 'yield'
    assignment[stmt_ty]:
    | a=NAME ':' b=expression c=['=' d=annotated_rhs { d }] {
        CHECK_VERSION(
            stmt_ty,
            6,
            "Variable annotation syntax is",
            _PyAST_AnnAssign(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), b, c, 1, EXTRA)
        ) }
    | a=('(' b=single_target ')' { b }
         | single_subscript_attribute_target) ':' b=expression c=['=' d=annotated_rhs { d }] {
        CHECK_VERSION(stmt_ty, 6, "Variable annotations syntax is", _PyAST_AnnAssign(a, b, c, 0, EXTRA)) }
    | a[asdl_expr_seq*]=(z=star_targets '=' { z })+ b=(yield_expr | star_expressions) !'=' tc=[TYPE_COMMENT] {
         _PyAST_Assign(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | a=single_target b=augassign ~ c=(yield_expr | star_expressions) {
         _PyAST_AugAssign(a, b->kind, c, EXTRA) }
    | invalid_assignment */
    fn parse_assignment(&mut self) -> Result<Option<AstRef>, SyntaxErrRef> {
        let p = self.it;

        // NAME ':' expression ['=' annotated_rhs ]
        if let Some(name) = eat_ident!(self) {
            if eat!(self, TokenValue::Colon).is_some() {
                let target = self.new_ast(
                    AstKind::Name {
                        name,
                        ctx: ExprContext::Store,
                    },
                    p..p + 1,
                );

                if let Some(expr) = self.parse_star_expressions()? {
                    if eat!(self, TokenValue::Equal).is_some() {
                        if let Some(arhs) = self.parse_annotated_rhs()? {
                            return Ok(Some(self.new_ast(
                                AstKind::AnnAssign {
                                    target,
                                    annotation: expr,
                                    value: AstOption(Some(arhs)),
                                },
                                p..self.it,
                            )));
                        }
                    } else {
                        return Ok(Some(self.new_ast(
                            AstKind::AnnAssign {
                                target,
                                annotation: expr,
                                value: AstOption(None),
                            },
                            p..self.it,
                        )));
                    }
                }
            }
            self.it = p;
        }

        // '(' single_target ')' ':' expression ['=' annotated_rhs ]
        if let Some(open_bracket) = eat!(self, TokenValue::OpenBracket) {
            let should_stop_brackets = !self.inside_brackets;
            self.inside_brackets = true;

            if let Some(single_target) = self.parse_single_target()? {
                if eat!(self, TokenValue::ClosedBracket).is_some() {
                    if should_stop_brackets {
                        self.inside_brackets = false;
                    }

                    if eat!(self, TokenValue::Colon).is_some() {
                        if let Some(expr) = self.parse_star_expressions()? {
                            if eat!(self, TokenValue::Equal).is_some() {
                                if let Some(arhs) = self.parse_annotated_rhs()? {
                                    return Ok(Some(self.new_ast(
                                        AstKind::AnnAssign {
                                            target: single_target,
                                            annotation: expr,
                                            value: AstOption(Some(arhs)),
                                        },
                                        p..self.it,
                                    )));
                                }
                            } else {
                                return Ok(Some(self.new_ast(
                                    AstKind::AnnAssign {
                                        target: single_target,
                                        annotation: expr,
                                        value: AstOption(None),
                                    },
                                    p..self.it,
                                )));
                            }
                        }
                    }
                } else {
                    let target_range =
                        range(&open_bracket.loc.range, &self.token_range(single_target));

                    return Err(self
                        .syntax_err()
                        .loc_msg(open_bracket.loc.range, "bracket not closed")
                        .annotation(
                            Level::Info,
                            target_range.clone(),
                            "for this statement",
                            false,
                        )
                        .suggestion(target_range.end, ")", "close the bracket")
                        .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(
                            true,
                        ));
                }
            } else {
                if should_stop_brackets {
                    self.inside_brackets = false;
                }
            }
            self.it = p;
        }

        // single_subscript_attribute_target ':' expression ['=' annotated_rhs ]
        if let Some(target) = self.parse_single_subscript_attribute_target()? {
            if eat!(self, TokenValue::Colon).is_some() {
                if let Some(expr) = self.parse_star_expressions()? {
                    if eat!(self, TokenValue::Equal).is_some() {
                        if let Some(arhs) = self.parse_annotated_rhs()? {
                            return Ok(Some(self.new_ast(
                                AstKind::AnnAssign {
                                    target,
                                    annotation: expr,
                                    value: AstOption(Some(arhs)),
                                },
                                p..self.it,
                            )));
                        }
                    } else {
                        return Ok(Some(self.new_ast(
                            AstKind::AnnAssign {
                                target,
                                annotation: expr,
                                value: AstOption(None),
                            },
                            p..self.it,
                        )));
                    }
                } 
            } 
            self.it = p;
        }

        // a[asdl_expr_seq*]=(z=star_targets '=' { z })+ b=(yield_expr | star_expressions) !'=' tc=[TYPE_COMMENT]
        if let Some(first_star_targets) = self.parse_star_targets()? {
            if matches!(self.peek_token(), token_value!(TokenValue::Equal)) {
                let mut chained_targets: Vec<&mut Ast, &BumpSync<'_>> =
                    Vec::<AstRef, _>::new_in(self.ast_arena);

                let mut last_equal = self.it;
                let mut last_could_parse = true;

                while eat!(self, TokenValue::Equal).is_some() {
                    last_equal = self.it;
                    if let Some(targets) = self.parse_star_targets()? {
                        chained_targets.push(targets);
                    } else {
                        last_could_parse = false;
                        break;
                    }
                }

                // Roll-back cause we expect the last equal to be an expression!
                self.it = last_equal;
                if last_could_parse {
                    chained_targets.pop();
                }

                // TODO: yield expression

                if let Some(expr) = self.parse_star_expressions()? {
                    let target;
                    if chained_targets.len() == 0 {
                        target = first_star_targets;
                    } else {
                        chained_targets.insert(0, first_star_targets);

                        let token_range = chained_targets[0].token_range.start
                            ..chained_targets.last().unwrap().token_range.end;
                        target = self.new_ast(
                            AstKind::ChainedTargets {
                                targets: AstVecOf::<AstRef>(chained_targets),
                            },
                            token_range,
                        );
                    }

                    // TODO: Type comment

                    return Ok(Some(self.new_ast(
                        AstKind::Assign {
                            target: target,
                            value: expr,
                        },
                        p..self.it,
                    )));
                } 
            } 
            self.it = p; // err ?
        }

        // TODO: Chained assign

        // TODO: Augmented assign

        /*[
        1 => TokenValue::Identifier(_),
        2 => TokenValue::ClosedBracket,
        3 => TokenValue::Equal] */

        // return Ok(Some(range(p.code_location, self.expect_expression()?)));
        //  }

        // Report errors if the last part is either genexp or a function call! Can't assign to those:
        // | t_primary genexp &t_lookahead
        // | t_primary '(' [arguments] ')' &t_lookahead

        Ok(None)
        /*
        let loc_p = loc!(self, p);
        Err(self.syntax_err()
            .loc_msg(loc_p.clone(), "expected an assignment statement")
            .suggestion(loc_p.start, "... = ...\n", "it looks like this")
            .suggestion(loc_p.start, "... : ... = ...\n", ".. or with a type specifier")
        )
         */
    }

    #[inline]
    fn next_token(&mut self) -> Option<Token> {
        let mut res = self.tokens.get(self.it);
        while self.inside_brackets && matches!(res, token_value!(TokenValue::NewLine)) {
            self.it += 1;
            res = self.tokens.get(self.it);
        }
        self.it += 1;
        res.cloned()
    }

    #[inline]
    fn peek_token(&mut self) -> Option<Token> {
        self.peek_nth_token(0)
    }

    #[inline]
    fn peek_nth_token(&mut self, n: usize) -> Option<Token> {
        let mut i = self.it;
        let mut res = None;

        for _ in 0..=n {
            res = self.tokens.get(i);
            while self.inside_brackets && matches!(res, token_value!(TokenValue::NewLine)) {
                self.it += 1;
                res = self.tokens.get(self.it);
            }
            i += 1;
        }
        res.cloned()
    }

    fn syntax_err(&self) -> SyntaxErrRef {
        self.parser_arena
            .alloc(SyntaxErr::new(self.filename.clone(), self.source))
    }
}
