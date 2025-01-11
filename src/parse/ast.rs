use std::{fmt::{self, Display, Formatter}, ops::Range};

use bumpalo::BumpSync;
use display_tree::{DisplayTree, Style};
use itertools::enumerate;

use super::{Atom, NumericLiteralRef, StringLiteralRef};

pub struct Strings(pub Vec<StringLiteralRef, &'static BumpSync<'static>>);

impl Display for Strings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (it, el) in enumerate(&self.0) {
            write!(f, "{}", el)?;
            if it != self.0.len() - 1 {
                f.write_str(",")?
            }
        }
        f.write_str("]")
    }
}

pub enum ConstantValue {
    String(Strings),
    Number(NumericLiteralRef),
    Bool(bool),
    None,
}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(strings) => write!(f, "{}", strings),
            Self::Number(number) => write!(f, "Number {}", number),
            Self::Bool(b) => write!(f, "{}", if *b { "True" } else { "False" }),
            Self::None => write!(f, "None"),
        }
    }
}


#[derive(Debug, DisplayTree)]
pub enum BinOp {
    Add,
    Sub,
    Mult,
    MatMult,
    Div,
    FloorDiv,
    Mod,
    Pow,
    
    BitShiftLeft,
    BitShiftRight,
    BitOr,
    BitXor,
    BitAnd,
    
    BoolAnd,
    BoolOr,

    LeftShift,
    RightShift,

    Or,
    And,

    Eq,
    NotEq,
    Less,
    LessOrEqual,
    Greater,
    GreaterOrEqual,

    In,
    NotIn,
    Is,
    IsNot,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug)]

pub enum UnaryOp {
    Add,
    Sub,
    Not,
    BitNot,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug)]
pub enum ExprContext {
    Load,
    Store,
    Del
}

impl Display for ExprContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct AstVecOf<T>(pub Vec<T, &'static BumpSync<'static>>);
pub type AstVec = AstVecOf<AstRef>;

impl<T> DisplayTree for AstVecOf<T> where T: DisplayTree,
{
    fn fmt(&self, f: &mut Formatter, style: Style) -> fmt::Result {
        for (it, el) in self.0.iter().enumerate() {
            write!(f, "[{}] ", it)?;
            DisplayTree::fmt(el, f, style)?;
            if it != self.0.len() - 1 {
                writeln!(f)?
            }
        }
        fmt::Result::Ok(())
    }
}

pub struct AstOption<T>(pub Option<T>);

impl<T> DisplayTree for AstOption<T>
where
    T: DisplayTree,
{
    fn fmt(&self, f: &mut Formatter, style: Style) -> fmt::Result {
        if let Some(el) = &self.0 {
            DisplayTree::fmt(el, f, style)?;
        }
        fmt::Result::Ok(())
    }
}

pub enum AstSingleOrMultiple<S, M> {
    Single(S),
    Multiple(M),
}

impl<S, M> DisplayTree for AstSingleOrMultiple<S, M> where S: DisplayTree, M: DisplayTree {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        match self {
            Self::Single(s) => DisplayTree::fmt(s, f, style),
            Self::Multiple(m) => DisplayTree::fmt(m, f, style)
        }
    }
}

#[derive(DisplayTree)]

pub enum AstKind {
    Module { 
        // List of statements
        #[tree]
        body: AstVec,
    },

    Blank, // Preserve this for program printing
    
    // List of statements on one line
    Statements {
        #[tree]
        statements: AstVec,
    },

    Return {
        #[tree]
        value: AstOption<AstRef>,
    },

    Name {
        #[tree]
        name: Atom,
        ctx: ExprContext,
    },

    Tuple {
        #[tree]
        targets: AstSingleOrMultiple<AstRef, AstVec>, 
        ctx: ExprContext,
    },

    // Chained targets, e.g. in assignment x = y = z = ...
    ChainedTargets {
        #[tree]
        targets: AstVec,
    },

    // *<target or expr>
    Starred {
        #[tree]
        value: AstRef, 
        ctx: ExprContext,
    },

    // **kwargs
    DoubleStarred {
        #[tree]
        value: AstRef, 
        ctx: ExprContext,
    },

    // <name> = <value> in arguments list
    KeywordArg {
        #[field_label]
        arg: Atom,

        #[field_label]
        #[tree]
        value: AstRef,

        ctx: ExprContext,
    },

    // <targets> = <value>
    Assign {
        #[field_label]
        #[tree]
        target: AstRef,

        #[field_label]
        #[tree]
        value: AstRef,
    },

    // <single target> : <type> = <value>
    AnnAssign {
        #[field_label]
        #[tree]
        single_target: AstRef,

        #[field_label]
        #[tree]
        annotation: AstRef,

        #[field_label]
        #[tree]
        value: AstOption<AstRef>,
    },

    AugAssign {
        #[tree]
        target: AstRef,
        
        #[node_label]
        op: BinOp,
        
        #[tree]
        value: AstRef,
    },
    
    BinOp {
        #[tree]
        left: AstRef,

        #[node_label]
        op: BinOp,

        #[tree]
        right: AstRef,
    },

    UnaryOp {
        #[node_label]
        op: UnaryOp,
        
        #[tree]
        operand: AstRef,
    },

    BoolOp {
        #[node_label]
        op: BinOp,
        
        #[tree]
        values: AstVec,
    },

    Compare {
        #[tree]
        #[field_label]
        left: AstRef,

        #[tree]
        #[field_label]
        ops: AstVecOf<BinOp>,

        #[tree]
        #[field_label]
        comparators: AstVec,
    },

    Constant {
        value: ConstantValue
    },

    Await {
        #[tree]
        value: AstRef,
    },

    Subscript {
        #[tree]
        value: AstRef,

        #[tree]
        #[field_label]
        slice: AstRef,

        ctx: ExprContext,
    },

    Call {
        #[tree]
        func: AstRef,

        #[tree]
        #[field_label]
        args: AstOption<AstRef>,

        #[tree]
        #[field_label]
        keywords: AstOption<AstRef>,
    },

    Slice {
        #[tree]
        #[field_label]
        lower: AstRef,

        #[tree]
        #[field_label]
        upper: AstRef,

        #[tree]
        #[field_label]
        step: AstOption<AstRef>,
    },

    // Only when an expression, such as a function call, appears as a statement by itself with its return value not used or stored.
    Expression {
        #[tree]
        value: AstRef,
    },

    IfExp {
        #[tree]
        #[field_label]
        test: AstRef,

        #[tree]
        #[field_label]
        body: AstRef,

        #[tree]
        #[field_label]
        orelse: AstRef,
    },

    NamedExpr {
        #[tree]
        #[field_label]
        target: AstRef,

        #[tree]
        #[field_label]
        value: AstRef,
    },

    Attribute {
        #[tree]
        value: AstRef,

        #[field_label]
        #[tree]
        attribute: Atom,

        ctx: ExprContext,
    },

    Walrus {
        #[field_label]
        #[tree]
        target: AstRef,

        #[field_label]
        #[tree]
        value: AstRef,
    },

    TypeAlias {
        #[tree]
        #[field_label]
        name: Atom,

        #[tree]
        #[field_label]
        type_params: AstOption<AstRef>,

        #[tree]
        #[field_label]
        value: AstRef,
    },

    TypeParamSeq {
        #[tree]
        #[field_label]
        params: AstVec,
    },

    TypeVarTuple {
        #[field_label]
        name: Atom,

        #[tree]
        #[field_label]
        default: AstOption<AstRef>,
    },

    ParamSpec {
        #[field_label]
        name: Atom,

        #[tree]
        #[field_label]
        default: AstOption<AstRef>,
    },

    TypeVar {
        #[tree]
        #[field_label]
        name: Atom,

        #[tree]
        #[field_label]
        bound: AstOption<AstRef>,

        #[tree]
        #[field_label]
        default: AstOption<AstRef>,
    },
}

pub struct Ast {
    pub id: usize,
    pub token_range: Range<usize>, // start..end span into the token array of collected tokens from the tokenizer
    
    pub kind: AstKind,
}

pub type AstRef = &'static mut Ast;

impl DisplayTree for AstRef {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        DisplayTree::fmt(&self.kind, f, style)
    }
}