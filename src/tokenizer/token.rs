use std::{num::NonZeroUsize, ops::Range};

use string_interner::symbol::SymbolU32;

pub type Atom = SymbolU32;

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

// TODO: Get rid of this since it's supposed to be for the AST
#[derive(Debug)]
pub struct StringLiteral {
    pub begin: Range<usize>,    // All the characters that began the string literal, e.g.  br##"
    pub end: Range<usize>,      // The characters that ended the quote, e.g "##

    pub is_byte_string: bool,
    pub content: Atom,          // The content of the string, without the quotes, suffixes and prefixes
    
    pub suffix: Option<Atom>,     // A literal optionally ends with an identifier suffix, e.g. "..."custom_suffix
}

#[derive(Debug)]
pub enum TokenValue<'mem> {
    WhiteSpace,          // a sequence of arbitrary unicode white space
    NewLine,             // \n

    Comment,             // // or /**/ 
    
    Directive(Atom),     // #[ident]
    Identifier(Atom),    // any sequence of alphanumeric unicode characters or _, starting with alphabetic or underscore
    
    String(&'mem StringLiteral), // any text surrounded with ', ", ''', or """; r, b, u prefixes and arbitrary suffixes
    Number,
    Order(usize),        // any integer followed by order suffix: 1st, 2nd, 3rd...

    Punctuation(Atom),   // a sequence of arbitrary unicode punctuation
    
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
pub struct Token<'mem> {
    pub value: TokenValue<'mem>,
    pub code_location: Range<usize>, // Begin and end bytes
}

pub type TokenIndex = NonZeroUsize; // Index within a BucketArray<Token>, non-zero for space optimization within Option<>
