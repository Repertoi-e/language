use std::{ops::Range, sync::atomic::{AtomicUsize, Ordering}};

use super::{ast::{Ast, AstKind, ConstantValue, NameContext}, AstOption, AstRef, AstVec, NumericLiteral, StringLiteral, Strings, SyntaxErr, Token, TokenValue, Tokenizer, TokensVec};
use crate::{annotations::Level, ArenaRef, AST_ARENA, AST_ARENA_HERD, KEYWORDS, PARSER_ARENA, PARSER_ARENA_HERD};

static AST_ID: AtomicUsize = AtomicUsize::new(0);

pub struct Parser<'source> {
    filename: Option<String>,
    source: &'source str,

    parser_arena: ArenaRef,
    ast_arena: ArenaRef,

    tokens: TokensVec, // Collected from tokenizer
    it: usize, // Token iterator

    inside_brackets: bool, // True while parsing brackets, so we count new line characters as white space 
}

macro_rules! expect {
    ($self:ident, $token:expr, $pattern:pat) => {{
        let token = $token;
        if matches!(token, $pattern) {
            Ok(0)
        } else {
            let location = loc!($self, &token);
            Err((location.clone(), $self.syntax_err().loc(location)))
        }
    }};
}

macro_rules! loc {
    ($self:ident, $token:expr) => {
        match $token {
            Some(t) => { t.loc.range.clone() }
            _ => { $self.source.len()..$self.source.len()+1 }
        }
    }
}

pub fn range(begin: &Range<usize>, end: &Range<usize>) -> Range<usize> {
    return begin.start..end.end;
}

macro_rules! token_value { ($pat:pat) => { Some(Token { value: $pat, .. }) } }


macro_rules! peek_and_eat_if_next_match_consecutive {
    ($self:ident, [$($n:expr => $pat:pat),+]) => {{
        let mut matched = true;
        $(
            if let Some(Token { value: $pat, .. }) = $self.peek_nth_token($n) {} 
            else {
                matched = false;
            }
        )+
        // If all patterns matched, consume tokens
        if matched {
            $(
                $n; $self.next_token();
            )+
            true
        } else {
            false
        }
    }};
}

macro_rules! peek_and_eat_if_next_match {
    ($self:ident, $n_first:expr => $first_pat:pat, [$($n:expr => $pat:pat),+]) => {{
        let p = $self.peek_nth_token($n_first);
        match p {
            Some(Token { value: $first_pat, loc: _ }) => {
                if peek_and_eat_if_next_match_consecutive!($self, [
                    $($n => $pat),+
                ]) {
                    $self.next_token(); 
                    p
                } else {
                    None 
                }
            }
            _ => None 
        }
    }};

    ($self:ident, $n_first:expr => $first_pat:pat) => {{
        let p = $self.peek_nth_token($n_first);
        match p {
            Some(Token { value: $first_pat, loc: _ }) => {
                $self.next_token();
                p
            }
            _ => None
        }
    }}
}

impl<'source> Parser<'source> {
    pub fn new(filename: Option<String>, input: &'source str) -> Result<Self, SyntaxErr<'source>> {
        Ok(Self {
            tokens: Tokenizer::new(filename.clone(), input).collect()?,
            filename,
            source: input,
            parser_arena: PARSER_ARENA.get_or(|| PARSER_ARENA_HERD.get()),
            ast_arena: AST_ARENA.get_or(|| AST_ARENA_HERD.get()),
            it: 0,
            inside_brackets: false,
        })
    }
    
    // 
    // A program is a series of statements 
    // 
    pub fn parse(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        let p = self.it;

        let mut statements: Vec<AstRef, _> = Vec::new_in(self.parser_arena);

        while let Some(statement) = self.parse_statement()? { 
            let next = self.peek_token();
            if matches!(next, token_value!(TokenValue::OpenBracket)) {
                let mut i = self.it + 1;
                while !matches!(self.peek_nth_token(i), token_value!(TokenValue::ClosedBracket)) {
                    let p = self.peek_nth_token(i);
                    if p.is_none() {
                        let start = next.unwrap().loc.range.start;
                        return Err(self.syntax_err()
                            .loc_msg(start..start+1, "bracket not closed")
                            .annotation(Level::Info, start..self.source.len(), "for this piece of code", false)
                            .in_interactive_interpreter_should_discard_and_instead_read_more_lines(true)
                        ) 
                    }
                    i += 1;
                }
            }
            statements.push(statement);
        }

        expect!(self, self.next_token(), None).map_err(|(_, s)| 
            s.msg("invalid statement")
        )?;
        // TODO: Better error message ^

        return Ok(Some(self.new_ast(AstKind::Module{ body: AstVec(statements) }, p..self.it)));
    }
}

impl<'source> Parser<'source> {
    fn new_ast(&mut self, kind: AstKind, token_range: Range<usize>) -> AstRef {
        self.ast_arena.alloc(Ast {
            id: AST_ID.fetch_add(1, Ordering::Relaxed),
            token_range,
            kind,
        })
    }

    fn parse_statement(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        if let Some(t) = self.peek_token() {
            if t.loc.leading_whitespace != 0 {
                return Err(self.syntax_err()
                    .loc_msg(t.range_of_leading_white_space(), "unexpected white space, this line is not part of any block, so it shouldn't have indentation")
                );
            }
        }

        match self.parse_assignment()? {
            Some(assignment) => {
                let range = self.token_range(assignment);
                expect!(self, self.next_token(), Some(Token { value: TokenValue::NewLine, ..}) | None)
                    .map_err(|(_, s)| 
                        s.msg("unexpected code after end of assignment")
                            .annotation(Level::Info, range.clone(), "this is the assignment", true)
                            .suggestion(range.end, ";", "add semicolon to separate statements on the same line")
                            .suggestion(range.end, "\n", "... or end the statement on this line")
                    )?;
                Ok(Some(assignment))
            }
            None => Ok(None)
        }
    }

    fn parse_expression(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        let p = self.it;

        if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Identifier(_)) {
            if let TokenValue::Identifier(name) = t.value {
                return Ok(Some(self.new_ast(AstKind::Name { name: name, ctx: NameContext::Load }, p..p+1)))
            }
            unreachable!();
        }

        /* 
        let loc_p = loc!(self, self.peek_token()?);
        Err(self.syntax_err()
            .loc_msg(loc_p, "expected an expression: any combination of parentheses and operations between variables and literals")
        )*/

        Ok(None)
    }

    fn parse_strings(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        // Consecutive strings get appended to each other
        
        let p = self.it;

        let mut strings = Vec::<StringLiteral, _>::new_in(self.parser_arena);
        while let Some(next) = self.peek_token() {
            if !matches!(next.value, TokenValue::String(_)) {
                break;
            }
            strings.push(self.reparse_string_literal(&next));
            self.next_token();
        }

        if strings.len() != 0 {
            Ok(Some(self.new_ast(AstKind::Constant { value: ConstantValue::String(Strings(strings)) }, p..self.it)))
        } else {
            Ok(None)
        }
    }

    fn reparse_string_literal(&mut self, t: &Token) -> StringLiteral {
        let mut tokenizer = Tokenizer::new(None, &self.source[t.loc.range.clone()]);
        let string_literal = tokenizer.parse_string_literal().expect("internal error; re-parsing string literal in parser was not succesful");
        string_literal.expect("internal error; re-parsed string literal was None")
    }

    fn reparse_numeric_literal(&mut self, t: &Token) -> NumericLiteral {
        let mut tokenizer = Tokenizer::new(None, &self.source[t.loc.range.clone()]);
        let numeric_literal = tokenizer.parse_numeric_literal().expect("internal error; re-parsing numeric literal in parser was not succesful");
        numeric_literal
    }

    /*

    atom:
    | NAME
    | 'True' 
    | 'False' 
    | 'None' 
    | strings
    | NUMBER
    |
    | TODO:
    | (tuple | group | genexp)
    | (list | listcomp)
    | (dict | set | dictcomp | setcomp)
    | '...' 
    */

    fn parse_atom(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        let p = self.it;
        
        if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Number) {
            let numeric_literal = self.reparse_numeric_literal(&t);
            return Ok(Some(self.new_ast(AstKind::Constant { value: ConstantValue::Number(numeric_literal) }, p..p+1)))
        }

        if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Identifier(_)) {
            if let TokenValue::Identifier(name) = t.value {
                return Ok(Some(self.new_ast(AstKind::Name { name: name, ctx: NameContext::Load }, p..p+1)))
            }
            unreachable!();
        }

        if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Keyword(_)) {
            if let TokenValue::Keyword(keyword) = t.value {
                if keyword == KEYWORDS.True {
                    return Ok(Some(self.new_ast(AstKind::Constant { value: ConstantValue::Bool(true) }, p..p+1)))
                } else if keyword == KEYWORDS.False { 
                    return Ok(Some(self.new_ast(AstKind::Constant { value: ConstantValue::Bool(false) }, p..p+1)))
                } else if keyword == KEYWORDS.None {
                    return Ok(Some(self.new_ast(AstKind::Constant { value: ConstantValue::None }, p..p+1)))
                } else {
                    self.it = p;
                }
            }
            unreachable!();
        }

        if let Some(strings) = self.parse_strings()? {
            return Ok(Some(strings));
        }

        Ok(None)
    }

    fn parse_single_subscript_attribute_target(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        let mut ast;
        if let Some(atom) = self.parse_atom()? {  // Start with an atom
            ast = atom;
        } else {
            return Ok(None);
        }

        let p = self.it;
        while let Some(_) = peek_and_eat_if_next_match!(self, 
            0 => /*TokenValue::OpenBracket | TokenValue::OpenSquareBracket | */ TokenValue::Dot // Lookahead
        ) {
            if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Identifier(_)) {
                if let TokenValue::Identifier(attr) = t.value {
                    ast = self.new_ast(AstKind::Attribute { value: ast, attribute: attr }, p..self.it);
                }
            } else {
                self.it = p; // err ?

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
        Ok(Some(ast))
    }

    fn token_range(&mut self, ast: &Ast) -> Range<usize> {
        let start = &self.tokens[ast.token_range.start].loc.range;
        let end = &self.tokens[ast.token_range.end-1].loc.range;
        range(start, end)
    }

    fn parse_single_target(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        let p = self.it;

        if let Some(target) = self.parse_single_subscript_attribute_target()? {
            Ok(Some(target))
        } else if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Identifier(_)) {
            if let TokenValue::Identifier(name) = t.value {
                return Ok(Some(self.new_ast(AstKind::Name { name: name, ctx: NameContext::Load}, p..p+1)))
            }
            unreachable!();
        } else if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::OpenBracket) {
            let should_stop_brackets = !self.inside_brackets;
            self.inside_brackets = true;

            // Handle recursive brackets
            if let Some(single_target) = self.parse_single_target()? {
                if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::ClosedBracket) {
                    if should_stop_brackets { self.inside_brackets = false; } 
                    
                    single_target.token_range = p..self.it;
                    Ok(Some(single_target))
                } else {
                    let target_range = range(&t.loc.range, &self.token_range(single_target));
                    Err(self.syntax_err()
                        .loc_msg(t.loc.range, "bracket not closed")
                        .annotation(Level::Info, target_range.clone(), "for this statement", false)
                        .suggestion(target_range.end, ")", "close the bracket")
                        .in_interactive_interpreter_should_discard_and_instead_read_more_lines(true)
                    )
                }
            } else {
                if should_stop_brackets { self.inside_brackets = false; } 
                self.it = p;
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }
    
    fn parse_annotated_rhs(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        // yield_expr or star_expressions
        self.parse_expression()
    }

    fn parse_assignment(&mut self) -> Result<Option<AstRef>, SyntaxErr<'source>> {
        let p = self.it;

        // NAME ':' expression ['=' annotated_rhs ] 
        if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Identifier(_), [1 => TokenValue::Colon]) {
            let target;
            if let TokenValue::Identifier(name) = t.value {
                target = self.new_ast(AstKind::Name { name: name, ctx: NameContext::Load }, p..p+1);
            } else {
                unreachable!();
            }
            
            if let Some(expr) = self.parse_expression()? {
                if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Equal) {
                    if let Some(arhs) = self.parse_annotated_rhs()? {
                        return Ok(Some(self.new_ast(AstKind::AnnAssign { 
                            target, annotation: expr, value: AstOption(Some(arhs)),
                        }, p..self.it)));
                    } else {
                        self.it = p;
                    }
                } else {
                    return Ok(Some(self.new_ast(AstKind::AnnAssign { 
                        target, annotation: expr, value: AstOption(None),
                    }, p..self.it)));
                }
            } else {
                self.it = p; // err?
            }
        } 

        // '(' single_target ')' ':' expression ['=' annotated_rhs ] 
        if let Some(t) = peek_and_eat_if_next_match!(self, 0 => TokenValue::OpenBracket) {
            let should_stop_brackets = !self.inside_brackets;
            self.inside_brackets = true;

            if let Some(single_target) = self.parse_single_target()? {
                if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::ClosedBracket) {
                    if should_stop_brackets { self.inside_brackets = false; }
                    
                    if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Colon) {
                        if let Some(expr) = self.parse_expression()? {
                            if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Equal) {
                                if let Some(arhs) = self.parse_annotated_rhs()? {
                                    return Ok(Some(self.new_ast(AstKind::AnnAssign { 
                                        target: single_target, annotation: expr, value: AstOption(Some(arhs)),
                                    }, p..self.it)));
                                } else {
                                    self.it = p; // err?
                                }
                            } else {
                                return Ok(Some(self.new_ast(AstKind::AnnAssign { 
                                    target: single_target, annotation: expr, value: AstOption(None),
                                }, p..self.it)));
                            }
                        }
                        else {
                            self.it = p; // err?
                        }
                    } else {
                        self.it = p; // err?
                    }
                } else {
                    let target_range = range(&t.loc.range, &self.token_range(single_target));
                    return Err(self.syntax_err()
                        .loc_msg(t.loc.range, "bracket not closed")
                        .annotation(Level::Info, target_range.clone(), "for this statement", false)
                        .suggestion(target_range.end, ")", "close the bracket")
                        .in_interactive_interpreter_should_discard_and_instead_read_more_lines(true)
                    )
                }
            } else {
                if should_stop_brackets { self.inside_brackets = false; }
                self.it = p;
            }
        }

        // single_subscript_attribute_target ':' expression ['=' annotated_rhs ] 
        if let Some(target) = self.parse_single_subscript_attribute_target()? {
            if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Colon) {
                if let Some(expr) = self.parse_expression()? {
                    if let Some(_) = peek_and_eat_if_next_match!(self, 0 => TokenValue::Equal) {
                        if let Some(arhs) = self.parse_annotated_rhs()? {
                            return Ok(Some(self.new_ast(AstKind::AnnAssign { 
                                target, annotation: expr, value: AstOption(Some(arhs)),
                            }, p..self.it)));
                        } else {
                            self.it = p; // err?
                        }
                    } else {
                        return Ok(Some(self.new_ast(AstKind::AnnAssign { 
                            target, annotation: expr, value: AstOption(None),
                        }, p..self.it)));
                    }
                }
                else {
                    self.it = p; // err?
                }
            } else {
                self.it = p; // err?
            }
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

    #[inline] fn next_token(&mut self) -> Option<Token> {
        let mut res = self.tokens.get(self.it);
        while self.inside_brackets && matches!(res, token_value!(TokenValue::NewLine))  
        {
            self.it += 1;
            res = self.tokens.get(self.it);
        }
        self.it += 1;
        println!("{:?}", res);
        res.cloned()
    }

    #[inline] fn peek_token(&mut self) -> Option<Token> {  self.peek_nth_token(0) }

    #[inline] fn peek_nth_token(&mut self, n: usize) -> Option<Token> { 
        let mut i = self.it;
        let mut res = None;

        for _ in 0..=n {
            res = self.tokens.get(i);
            while self.inside_brackets && matches!(res, token_value!(TokenValue::NewLine))
            {
                self.it += 1;
                res = self.tokens.get(self.it);
            }
            i += 1;
        }
        res.cloned()
    }

    fn syntax_err(&self) -> SyntaxErr<'source> { SyntaxErr::new(self.filename.clone(), self.source) }
}