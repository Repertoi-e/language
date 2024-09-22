use std::ops::Range;

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

#[derive(Debug)]
pub struct StringLiteral {
    pub code_location: Range<usize>,  // Begin and end bytes of entire literal

    pub begin_quote: Range<usize>,    // All the characters that began the string literal, e.g.  br##"
    pub end_quote: Range<usize>,      // The characters that ended the quote, e.g "##

    pub is_byte_string: bool,
    pub content: Atom,            // The content of the string, without the quotes, suffixes and prefixes
    
    pub suffix: Option<Atom>,     // A literal optionally ends with an identifier suffix, e.g. "..."custom_suffix
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

    pub suffix: Option<Atom>,     // A literal optionally ends with an identifier suffix, e.g. ...f32
}

#[derive(Clone, Debug)]
pub enum TokenValue {
    NewLine,             // \n

    Identifier(Atom),    // any sequence of alphanumeric unicode characters or _, starting with alphabetic or underscore
    Keyword(Atom),       // any identifier which matches a keyword

    String(Atom),        // any text surrounded with ', ", ''', or """; r, b, u prefixes and arbitrary suffixes
    Number,

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