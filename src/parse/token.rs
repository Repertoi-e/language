use std::{fmt::Display, ops::Range};

use display_tree::DisplayTree;
use string_interner::symbol::SymbolU32;

use crate::STRING_ARENA;

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Atom(pub SymbolU32);

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.value)
    }
}

impl DisplayTree for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter, _style: display_tree::Style) -> std::fmt::Result {
        write!(f, "{:?}", STRING_ARENA.lock().unwrap().resolve(self.0).unwrap())
    }
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum Integer {
    i8(i8),
    i16(i16),
    i32(i32),
    i64(i64),
    i128(i128),

    u8(u8),
    u16(u16),
    u32(u32),
    u64(u64),
    u128(u128),

    offset(isize),
    size(usize),

    Big(rug::Integer)
}

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Integer::i8(i) => write!(f, "{}", i),
            Integer::i16(i) => write!(f, "{}", i),
            Integer::i32(i) => write!(f, "{}", i),
            Integer::i64(i) => write!(f, "{}", i),
            Integer::i128(i) => write!(f, "{}", i),
            Integer::u8(i) => write!(f, "{}", i),
            Integer::u16(i) => write!(f, "{}", i),
            Integer::u32(i) => write!(f, "{}", i),
            Integer::u64(i) => write!(f, "{}", i),
            Integer::u128(i) => write!(f, "{}", i),
            Integer::offset(i) => write!(f, "{}", i),
            Integer::size(i) => write!(f, "{}", i),
            Integer::Big(i) => write!(f, "{}", i),
        }
    }
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum Float {
    f16(f16),
    f32(f32),
    f64(f64),
    f128(f128),
    Big(rug::Float)
}

impl Display for Float {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Float::f16(fl) => write!(f, "{:?}", fl),
            Float::f32(fl) => write!(f, "{}", fl),
            Float::f64(fl) => write!(f, "{}", fl),
            Float::f128(fl) => write!(f, "{:?}", fl),
            Float::Big(fl) => write!(f, "{}", fl),
        }
    }
}

#[derive(Debug)]
pub enum Number {
    Integer(Integer),
    Float(Float),
    Rational(rug::Rational),
    Complex(rug::Complex),
}

#[derive(Debug)]
pub struct StringLiteral {
    pub code_location: Range<usize>,  // Begin and end bytes of entire literal

    pub begin_quote: Range<usize>,    // All the characters that began the string literal, e.g.  br##"
    pub end_quote: Range<usize>,      // The characters that ended the quote, e.g "##

    pub is_byte_string: bool,
    pub content: Atom,            // The content of the string, without the quotes, suffixes and prefixes
    
    pub suffix: Option<Atom>,     // A literal optionally ends with an identifier suffix, e.g. "..."custom_suffix
}

impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", STRING_ARENA.lock().unwrap().resolve(self.content.0).unwrap())
    }
}

#[derive(Debug)]
pub struct NumericLiteral {
    pub code_location: Range<usize>,  // Begin and end bytes of entire literal

    pub base: Option<usize>,          // 2, 8 or 16 for integers and 10 for decimal numbers, 16 for hex floats 

    //
    // Always true: end_integer_part <= end_fractional_part <= end_number_part
    //
    //    246
    //       ╷
    //       └ end_integer_part = end_fractional_part = end_number_part = 3
    //
    //    0xAB46
    //          ╷
    //          └ end_integer_part = end_fractional_part = end_number_part = 6
    //
    //    12_3.4_56e789f32
    //        ╷    ╷   ╷
    //        |    |   └ end_number_part = 13
    //        |    └ end_fractional_part = 9
    //        └ end_integer_part = 4
    //
    //    246.
    //       ╷╷
    //       |└ end_fractional_part = end_number_part = 4
    //       └ end_integer_part = 3
    //
    //    1234e89
    //        ╷  ╷
    //        |  └ end_number_part = 7
    //        └ end_integer_part = end_fractional_part = 4
    //
    //    0x.2p-1
    //      | ╷  ╷
    //      | |  └ end_number_part = 7
    //      | └ end_fractional_part = 4
    //      └ end_integer_part = 2
    // 
    // therefore to check if number has fractional part: end_integer_part != end_fractional_part,
    // and to test for exponent part:  end_fractional_part != end_number_part
    //
    pub end_integer_part: usize,
    pub end_fractional_part: usize,
    pub end_number_part: usize,

    pub value: Number,

    pub suffix: Option<Atom>,     // A literal optionally ends with an identifier suffix, e.g. ...f32
}

// implt display for NumericLiteral
impl Display for NumericLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.value {
            Number::Integer(int) => write!(f, "{}", int),
            Number::Float(float) => write!(f, "{}", float),
            Number::Rational(rational) => write!(f, "{}", rational),
            Number::Complex(complex) => write!(f, "{}", complex),
        }
    }
}

pub type StringLiteralRef = &'static StringLiteral;
pub type NumericLiteralRef = &'static NumericLiteral;

#[derive(Clone, Debug)]
pub enum TokenValue {
    NewLine,             // \n

    Identifier(Atom),    // any sequence of alphanumeric unicode characters or _, starting with alphabetic or underscore
    Keyword(Atom),       // any identifier which matched a keyword

    String(StringLiteralRef),    // any text surrounded with ', ", ''', or """; r, b, u prefixes and arbitrary suffixes
    Number(NumericLiteralRef),   // any integer, float or imaginary number. At this stage they are initialized to Integer::Big, Float::Big or Float::f32

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
    DivideFloorEqual,    // "//="
    DivideFloor,         // "//"
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

// Ranges are in byte start..end in the UTF-8 source code
#[derive(Clone, Debug)]
pub struct CodeLocation {
    pub range: Range<usize>, // Begin and end bytes
    
    // Used to preserve program structure to be able to print the program back in original form.
    // To get into ranges:
    //
    // (range.start-leading_whitespace)..range.start
    // range.end..(range.end+trailing_whitespace)
    //
    pub leading_whitespace: usize,  // the number of bytes of whitespace before range.start
    pub trailing_whitespace: usize, // the number of bytes of whitespace after range.end
}

#[derive(Clone, Debug)]
pub struct Token {
    pub value: TokenValue, // @TODO This is only 8 bytes
    pub loc: CodeLocation, // ...while this is 32. Maybe try to reduce the size?
}

impl Token {
    pub fn range_of_leading_white_space(&self) -> Range<usize> {
        self.loc.range.start-self.loc.leading_whitespace..self.loc.range.start
    }   

    pub fn range_of_trailing_white_space(&self) -> Range<usize> {
        self.loc.range.end..self.loc.range.end+self.loc.trailing_whitespace
    }
}