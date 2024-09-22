use std::{fmt::Display, ops::Range};

use bumpalo::BumpSync;
use display_tree::DisplayTree;
use itertools::enumerate;

use crate::STRING_ARENA;

use super::{Atom, NumericLiteral, StringLiteral};

pub struct Strings(pub Vec<StringLiteral, &'static BumpSync<'static>>);

impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", STRING_ARENA.lock().unwrap().resolve(self.content).unwrap())
    }
}

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
    Number(NumericLiteral),
    Bool(bool),
    None,
}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(strings) => write!(f, "{}", strings),
            Self::Number(_) => write!(f, "Number"),
            Self::Bool(bool) => write!(f, "{}", bool),
            Self::None => write!(f, "None"),
        }
    }
}


#[derive(Debug)]

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
    BoolOr
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
pub enum NameContext {
    Load,
    Store,
    Del
}

impl Display for NameContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct AstVec(pub Vec<AstRef, &'static BumpSync<'static>>);

pub struct AstOption(pub Option<AstRef>);

impl DisplayTree for AstOption {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        if let Some(el) = &self.0 {
            DisplayTree::fmt(el, f, style)?;
        }
        std::fmt::Result::Ok(())
    }
}

impl DisplayTree for AstVec {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        for (it, el) in enumerate(&self.0) {
            write!(f, "[{}] ", it)?;
            DisplayTree::fmt(el, f, style)?;
            if it != self.0.len() - 1 {
                writeln!(f, "")?
            }
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(DisplayTree)]

pub enum AstKind {
    Module { 
        // List of statements
        #[tree]
        body: AstVec,
    },

    Name {
        name: Atom,
        ctx: NameContext,
    },

    Assign {
        #[tree]
        targets: AstVec,
        #[tree]
        value: AstRef,
    },

    AnnAssign {
        #[tree]
        target: AstRef,

        #[tree]
        annotation: AstRef,

        #[tree]
        value: AstOption,
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
        op: BinOp,
        #[tree]
        operand: AstRef,
    },

    Constant {
        value: ConstantValue
    },

    // Only when an expression, such as a function call, appears as a statement by itself with its return value not used or stored.
    Expression {
        #[tree]
        value: AstRef,
    },

    Attribute {
        #[tree]
        value: AstRef,

        attribute: Atom,
    },

    Walrus {
        #[tree]
        target: AstRef,

        #[tree]
        value: AstRef,
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