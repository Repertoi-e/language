use std::{num::NonZeroUsize, ops::Range};

use bumpalo::Bump;

use string_interner::symbol::SymbolU32;
type Atom = SymbolU32;

pub enum IntegerValue {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    // IBig(BigInt),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    // UBig(BigUint),
}

pub struct Integer {
    size_in_bits: i8,
    signed: bool,
    value: IntegerValue
}

pub enum FloatValue {
    F32(f32),
    F64(f64)
}

#[derive(Debug)]
pub struct StringLiteral {
    pub begin: Range<usize>,    // All the characters that began the string literal, e.g.  br##"
    pub end: Range<usize>,      // The characters that ended the quote, e.g "##

    pub is_byte_string: bool,
    pub content: Atom,          // The content of the string, without the quotes, suffixes and prefixes
    
    pub suffix: Option<Atom>,     // A literal optionally ends with an identifier suffix, e.g. "..."custom_suffix
}

#[derive(Debug)]
pub enum TokenValue<'s> {
    WhiteSpace,          // a sequence of arbitrary unicode white space
    NewLine,             // \n

    Comment,             // // or /**/ 
    
    Directive(Atom),     // #[ident]
    Identifier(Atom),    // any sequence of alphanumeric unicode characters or _, starting with alphabetic or underscore

    As,       // as
    With,     // with
    In,       // in
    Is,       // is

    Assert,   // assert
    Async,    // async
    Await,    // await

    Class,    // class
    Struct,   // struct

    Def,      // def
    Return,   // return
    Yield,    // yield

    Del,      // del
    
    If,       // if
    Elif,     // elif
    Else,     // else
    
    Raise,    // raise
    Try,      // try
    Except,   // except
    Finally,  // finally
    
    While,    // while
    For,      // for
    Break,    // break
    Continue, // continue
    Pass,     // pass

    Import,   // import
    From,     // from
    
    Global,   // global
    NonLocal, // nonlocal
    Lambda,   // lambda
    
    String(Box<StringLiteral, &'s Bump>), // any text surrounded with ', ", ''', or """; r, b, u prefixes and arbitrary suffixes
    Number,

    True,                // True
    False,               // False
    
    First,               // First
    Last,                // Last
    Order(usize),        // any integer followed by order suffix: 1st, 2nd, 3rd...

    Punctuation,         // a sequence of arbitrary unicode punctuation
    
    OpenBracket,         // (
    ClosedBracket,       // )

    OpenSquareBracket,   // [
    ClosedSquareBracket, // ]

    OpenCurlyBracket,    // {
    ClosedCurlyBracket,  // }

    Ellipsis,            // "..."
    DotDot,              // ".."
    Dot,                 // "."

    ThinArrow,           // "->"
    ThickArrow,          // "=>"

    EqualEqual,          // "=="
    NotEqual,            // "!="
    Equal,               // "="

    And,                 // "&&"
    Or,                  // "||"
    Not,                 // "!"
    
    KeywordAnd,          // and
    KeywordOr,           // or
    KeywordNot,          // not

    BitwiseNot,          // "~"
    BitwiseOrEqual,      // "|="
    BitwiseOr,           // "|"
    BitwiseAndEqual,     // "&="
    BitwiseAnd,          // "&"

    Comma,               // ","
    Colon,               // ":"
    ColonColon,          // "::"
    Walrus,              // ":="
    SemiColon,           // ";"

    PlusEqual,           // "+="
    Plus,                // "+"
    MinusEqual,          // "-="
    Minus,               // "-"
    PowerEqual,          // "**="
    Power,               // "**"
    TimesEqual,          // "*="
    Times,               // "*"
    DivideFloorEqual,    // "/_="
    DivideFloor,         // "/_"
    DivideEqual,         // "/="
    Divide,              // "/"
    ModEqual,            // "%="
    Mod,                 // "%"

    ShiftLeftEqual,      // "<<="
    ShiftLeft,           // "<<"
    ShiftRightEqual,     // ">>="
    ShiftRight,          // ">>"

    Spaceship,           // "<=>"
    LessOrEqual,         // "<="
    Less,                // "<"
    GreaterOrEqual,      // ">="
    Greater,             // ">"

    AtEqual,             // "@="
    At,                  // "@"

    Dollar,              // "$"
    QuestionMark,        // "?"
    Hat,                 // "^"
}

#[derive(Debug)]
pub struct Token<'s> {
    pub value: TokenValue<'s>,
    pub code_location: Range<usize>, // Begin and end bytes
}

// Index within a BucketArray<Token>
pub type TokenIndex = NonZeroUsize;
