use std::{fmt::{write, Display}, mem, ops::Range};

use bumpalo::Bump;
use display_tree::DisplayTree;
use itertools::enumerate;

use crate::STRING_ARENA;

use super::{Atom, NumericLiteral, StringLiteral};

pub struct Strings<'mem>(pub Vec<StringLiteral, &'mem Bump>);

impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}", STRING_ARENA.lock().unwrap().resolve(self.content))
    }
}

impl<'mem> Display for Strings<'mem> {
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

pub enum ConstantValue<'mem> {
    String(Strings<'mem>),
    Number(&'mem NumericLiteral),
    Bool(bool),
    None,
}

impl<'mem> Display for ConstantValue<'mem> {
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

pub struct AstVec<'mem>(pub Vec<&'mem Ast<'mem>, &'mem Bump>);

pub struct AstOption<'mem>(pub Option<&'mem Ast<'mem>>);

impl<'mem> DisplayTree for AstOption<'mem> {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        if let Some(el) = self.0 {
            DisplayTree::fmt(el, f, style)?;
        }
        std::fmt::Result::Ok(())
    }
}

impl<'mem> DisplayTree for AstVec<'mem> {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        for (it, el) in enumerate(&self.0) {
            write!(f, "[{}] ", it)?;
            DisplayTree::fmt(*el, f, style)?;
            if it != self.0.len() - 1 {
                writeln!(f, "")?
            }
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(DisplayTree)]

pub enum AstKind<'mem> {
    Module { 
        // List of statements
        #[tree]
        body: AstVec<'mem>,
    },

    Name {
        name: Atom,
        ctx: NameContext,
    },

    Assign {
        #[tree]
        targets: AstVec<'mem>,
        #[tree]
        value: &'mem Ast<'mem>,
    },

    AnnAssign {
        #[tree]
        target: &'mem Ast<'mem>,

        #[tree]
        annotation: &'mem Ast<'mem>,

        #[tree]
        value: AstOption<'mem>,
    },

    AugAssign {
        #[tree]
        target: &'mem Ast<'mem>,
        #[node_label]
        op: BinOp,
        #[tree]
        value: &'mem Ast<'mem>,
    },
    
    BinOp {
        #[tree]
        left: &'mem Ast<'mem>,
        #[node_label]
        op: BinOp,
        #[tree]
        right: &'mem Ast<'mem>,
    },

    UnaryOp {
        op: BinOp,
        #[tree]
        operand: &'mem Ast<'mem>,
    },

    Constant {
        value: ConstantValue<'mem>
    },

    // Only when an expression, such as a function call, appears as a statement by itself with its return value not used or stored.
    Expression {
        #[tree]
        value: &'mem Ast<'mem>,
    },

    Attribute {
        #[tree]
        value: &'mem Ast<'mem>,

        attribute: Atom,
    },

    Walrus {
        #[tree]
        target: &'mem Ast<'mem>,

        #[tree]
        value: &'mem Ast<'mem>,
    },
}


pub struct Ast<'mem> {
    pub id: usize,
    pub token_range: Range<usize>, // start..end span into the token array of collected tokens from the tokenizer
    
    pub kind: AstKind<'mem>,
}

impl<'mem> DisplayTree for Ast<'mem> {
    fn fmt(&self, f: &mut std::fmt::Formatter, style: display_tree::Style) -> std::fmt::Result {
        DisplayTree::fmt(&self.kind, f, style)
    }
}