use anstyle::{AnsiColor, Reset, RgbColor};
use bumpalo::Bump;
use clap::Parser;

use itertools::enumerate;
use num_bigint::{BigInt, BigUint};
use rand::Rng;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use std::cmp::{max, min};
use std::ops::Range;
use std::panic::{set_hook, take_hook};
use std::{fs, panic};

use unicode_properties::{GeneralCategoryGroup, UnicodeGeneralCategory};

mod annotations;

#[derive(Parser, Debug)]
#[command(version = "0.0.1", about = "Interpreter and compiler for a language.", long_about = None)]
struct Args {
    #[arg(help = "The file to start running from.")]
    file: Option<String>,

    #[arg(short, long, default_value = "", help = "Parse and interpret a string before the beginning of the program.")]
    add: String,

    #[arg(short, long, default_value = "", help = "Runs the provided string as a standalone program.")]
    run: String,
}

enum IntegerValue {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    IBig(BigInt),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    UBig(BigUint),
}

struct Integer {
    size_in_bits: i8,
    signed: bool,
    value: IntegerValue
}

enum FloatValue {
    F32(f32),
    F64(f64)
}

#[derive(Clone, Debug)]
enum StringLiteralType {
    String(String),
    Bytes(Vec<u8>)
}

#[derive(Clone, Debug)]
struct StringLiteral<'a> {
    is_raw: bool,      // Helper bool to prevent the need to parse 'begin'
    is_byte: bool,    // Helper bool to prevent the need to parse 'begin'

    begin: &'a str,    // All the characters that began the string literal, e.g.  br##"
    end: &'a str,      // The characters that ended the quote, e.g "##

    content: StringLiteralType,  // The content of the string, without the quotes, suffixes and prefixes
    
    suffix: &'a str,   // A literal optionally ends with an identifier suffix, e.g. "..."custom_suffix
}

#[derive(Clone, Debug)]
enum TokenValue<'a> {
    WhiteSpace,    // a sequence of arbitrary unicode white space
    NewLine,       // \n

    Comment,       // // or /**/ 
    
    Directive,     // #[ident]
    Identifier,    // any sequence of alphanumeric unicode characters or _, starting with alphabetic or underscore


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
    
    String(StringLiteral<'a>), // any text surrounded with ', ", ''', or """; r, b, u prefixes and arbitrary suffixes
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
struct Token<'a> {
    value: TokenValue<'a>,
    code_location: Range<usize>, // Begin and end bytes
}

struct Tokenizer<'a> {
    filename: Option<&'a str>,
    source: &'a str,

    it: &'a [u8],  // Byte iterator

    bump: &'a Bump,
}

fn from_hex(c: char) -> u32 {
    match c {
        '0'..='9' => (c as u32) - ('0' as u32),
        'a'..='f' => (c as u32) - ('a' as u32) + 10,
        'A'..='F' => (c as u32) - ('A' as u32) + 10,
        _ => u32::MAX
    }
}

fn is_ident(ch: char, first_char: bool) -> bool {
    if first_char {
        return ch.is_alphabetic() || ch == '_';
    } else {
        return ch.is_alphanumeric() || ch == '_';
    }
}

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111;

/// Returns the initial codepoint accumulator for the first byte.
/// The first byte is special, only want bottom 5 bits for width 2, 4 bits
/// for width 3, and 3 bits for width 4.
#[inline]
const fn utf8_first_byte(byte: u8, width: u32) -> u32 { (byte & (0x7F >> width)) as u32 }

/// Returns the value of `ch` updated with continuation byte `byte`.
#[inline]
const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 { (ch << 6) | (byte & CONT_MASK) as u32 }

fn next_code_point_unchecked<'a>(bytes: &[u8]) -> char {
    // Decode UTF-8
    let x = bytes[0];
    if x < 128 { return unsafe { char::from_u32_unchecked(x as u32) } }

    // Multibyte case follows
    // Decode from a byte combination out of: [[[x y] z] w]
    // NOTE: Performance is sensitive to the exact formulation here
    let init = utf8_first_byte(x, 2);
    // SAFETY: `bytes` produces an UTF-8-like string,
    // so the indexing must produce a value here.
    let y = bytes[1];
    let mut ch = utf8_acc_cont_byte(init, y);
    if x >= 0xE0 {
        // [[x y z] w] case
        // 5th bit in 0xE0 .. 0xEF is always clear, so `init` is still valid
        // SAFETY: `bytes` produces an UTF-8-like string,
        // so the indexing must produce a value here.
        let y_z = utf8_acc_cont_byte((y & CONT_MASK) as u32, bytes[2]);
        ch = init << 12 | y_z;
        if x >= 0xF0 {
            // [x y z w] case
            // use only the lower 3 bits of `init`
            // SAFETY: `bytes` produces an UTF-8-like string,
            // so the indexing must produce a value here.
            ch = (init & 7) << 18 | utf8_acc_cont_byte(y_z,  bytes[3]);
        }
    }
    unsafe { char::from_u32_unchecked(ch) }
}

fn next_code_point(bytes: &[u8]) -> Option<char> {
    if bytes.len() == 0 { return None; }
    Some(next_code_point_unchecked(bytes))
}

fn panic_for_compiler_error() {
    panic::set_hook(Box::new(|_| {})); // Remove 'thread '...' panicked at ... ' message, since now we're just reporting a compiler error
    panic!();
}

impl<'a> Tokenizer<'a> {
    fn new(filename: Option<&'a str>, input: &'a str, bump: &'a Bump) -> Tokenizer<'a> {
        Tokenizer { 
            filename: filename,
            source: input,
            it: input.as_bytes(),
            bump: bump,
        }
    }

    #[inline]
    fn new_token(&self, value: TokenValue<'a>, range: Range<usize>) -> &'a Token<'a> {
        self.bump.alloc(Token { value: value, code_location: range })
    }

    fn new_token_and_advance(&mut self, value: TokenValue<'a>, range: Range<usize>) -> &'a Token<'a> {
        self.advance_bytes(range.len());
        self.bump.alloc(Token { value: value, code_location: range })
    }

    #[inline]
    fn peek_nth(&self, i: usize) -> Option<u8> { self.it.get(i).map(|&val| val) }
    
    #[inline]
    fn peek_nth_is(&self, i: usize, b: u8) -> bool { self.peek_nth(i).take_if(|x| *x == b).is_some() }

    #[inline]
    fn peek(&self) -> Option<u8> { self.peek_nth(0) }

    #[inline]
    fn peek_cp(&self) -> Option<(usize, char)> { 
        next_code_point(self.it).map(|ch| (self.ptr(), ch))
    }

    #[inline]
    fn next(&mut self) -> Option<(usize, char)> {
        return if let Some(ch) = next_code_point(self.it) {
            let p = self.ptr();
            self.it = &self.it[ch.len_utf8()..];
            Some((p, ch))
        } else {
            None
        }
    }

    #[inline]
    fn advance_bytes(&mut self, byte_count: usize) {
        self.it = &self.it[byte_count..];
    }

    #[inline]
    fn ptr(&self) -> usize { (self.it.as_ptr() as usize) - (self.source.as_ptr() as usize) }

    #[inline]
    fn advance_cp(&mut self, count: usize) {
        for _ in 0..count {
            if let Some(ch) = next_code_point(self.it) {
                self.it = &self.it[ch.len_utf8()..];
            } else {
                self.panic_and_syntax_err(self.ptr()..self.ptr()+count, format!("internal error; tried to advance parse pointer by {} code points here, but failed", count).as_str())
            }
        }
    }
    
    fn match_sequence(&mut self, sequence: &str) -> bool {
        self.it.starts_with(sequence.as_bytes())
    }

    fn match_sequence_expect_and_eat(&mut self, sequence: &str) -> usize {
        let p = self.ptr();
        if !self.match_sequence(sequence) {
            self.panic_and_syntax_err(p..p+sequence.len(), &format!("expected \"{}\"", sequence));
        }
        self.advance_bytes(sequence.len());
        p
    }

    fn eat_multiline_comment(&mut self) -> &'a Token<'a> {
        let p = self.match_sequence_expect_and_eat("/*");

        let mut did_recurse = false;
        while !self.match_sequence("*/") {
            if self.next().is_none() {
                self.panic_and_syntax_err_with_suggestions(
                    p..self.source.len(), 
                    if !did_recurse { "multiline comment was not closed" }
                    else { "multiline comment was not closed, in nested multiline comments each one must be closed" },
                    &[(self.source.len(), "*/", "close the comment")]
                );
            }
            if self.match_sequence("/*") {
                did_recurse = true;
                self.eat_multiline_comment();
            }
        }
        self.match_sequence_expect_and_eat("*/");
        self.new_token(TokenValue::Comment, p..self.ptr())
    }

    fn try_eat_identifier(&mut self) -> Option<&'a Token<'a>> {
        if is_ident(self.peek_cp().unwrap_or_default().1, true) {
            let (_, range) = self.expect_and_eat_ident();
            Some(self.new_token(TokenValue::Identifier, range))
        } else {
            None
        }
    }
    
    fn expect_and_eat_ident(&mut self) -> (&'a str, Range<usize>) {
        if !is_ident(self.peek_cp().unwrap_or_default().1, true) {
            self.panic_and_syntax_err(self.ptr()..self.ptr()+1, "invalid start of identifier, must be an alphabetic character or _");
        }

        let p = self.ptr();
        while self.peek_cp().take_if(|(_, x)| is_ident(*x, false)).is_some() {
            self.next();
        }
        
        (&self.source[p..self.ptr()], p..self.ptr())
    }
    
    fn try_eat_string_literal(&mut self) -> Option<&'a Token<'a>> {
        match self.peek() {
            Some(mut ch) => {
                let begin_p = self.ptr();

                let mut is_byte = false;
                let mut is_raw = false;
                let mut is_unicode = false;

                let mut offset = 0;

                if ch.is_ascii_alphabetic() {
                    while !is_raw || !is_byte {
                        ch = self.peek_nth(offset).unwrap_or_default();
                        if !is_byte && (ch == b'b' || ch == b'B') {
                            is_byte = true;
                            offset += 1;
                        } else if !is_raw && (ch == b'r' || ch == b'R') {
                            is_raw = true;
                            offset += 1;
                        } else if !is_unicode && (ch == b'u' || ch == b'U') { // Skip unicode specifier, as strings are unicode by default anyway
                            is_unicode = true;
                            offset += 1;
                        } else {
                            break;
                        }
                    }
                }

                // Parse a number of hashes for raw string, to build the expected terminating sequence
                let mut parse_until = bumpalo::collections::Vec::with_capacity_in(256, self.bump);
                if is_raw {
                    while self.peek_nth_is(offset,  b'#') {
                        parse_until.push(b'#');
                        offset += 1;
                    }
                }

                // Expect quote, otherwise return None. Don't throw an error since we're just tip-toeing to see if
                // it's a valid string literal, and not necessarily expecting one. Outside of this function the code 
                // probably starts testing for an identifier.
                if self.peek_nth(offset).take_if(|x| *x == b'\'' || *x == b'"').is_none() {
                    return None;
                }

                self.advance_bytes(offset); // So far we've just parsed ASCII characters

                let mut is_multiline = is_raw;
                if self.match_sequence("\"\"\"") {
                    is_multiline = true;
                    offset += 2;
                    self.advance_bytes(3);
                    parse_until.insert(0, b'\"');
                    parse_until.insert(0, b'\"');
                    parse_until.insert(0, b'\"');
                } else if self.match_sequence("'''") {
                    is_multiline = true;
                    offset += 2;
                    self.advance_bytes(3);
                    parse_until.insert(0, b'\'');
                    parse_until.insert(0, b'\'');
                    parse_until.insert(0, b'\'');
                } else {
                    let quote = self.peek().unwrap();
                    self.advance_bytes(1);
                    parse_until.insert(0, quote);
                };

                let parse_until_str = std::str::from_utf8(&parse_until).unwrap_or(" ");

                let mut content = String::new();
                while !self.match_sequence(&parse_until_str) {
                    match self.next() {
                        Some((p, ch)) => {
                            if !is_raw {
                                // Handle string continue, i.e. escaping newline
                                if ch == '\\' && self.peek().take_if(|x| *x == b'\n').is_some() {
                                    self.advance_bytes(1);
                                    continue;
                                }
                                
                                // Handle unicode sequences
                                if ch == '\\' && self.peek().take_if(|x| x.eq_ignore_ascii_case(&b'u')).is_some() {
                                    let mut num_digits = 8; // 8 for 'U'
                                    if let Some((_, 'u')) = self.next() {
                                        num_digits = 4; // 4 for 'u'
                                    }
                
                                    let mut sum = 0;
                                    for _ in 0..num_digits {
                                        let it: Option<(usize, char)> = self.next();
                                        if it.is_none_or(|(_, x)| !x.is_ascii_hexdigit()) { 
                                            self.panic_and_syntax_err_with_help(
                                                p..p+2+num_digits, 
                                                "expected unicode escape sequence in the form \\uXXXX or \\UXXXXXXXX, where X is a hexadecimal digit",
                                                self.ptr()-1..self.ptr(), 
                                                "this character is the problem"
                                            ); 
                                        }
                                        sum = sum * 16 + from_hex(it.unwrap().1);
                                    }
                                    content.push(char::from_u32(sum).ok_or_else(|| {
                                        self.panic_and_syntax_err(
                                            p..p+2+num_digits, 
                                            "couldn't decode the invalid unicode escape sequence"
                                        ); 
                                    }).unwrap());
                                    continue;
                                }

                                // Handle other escapes
                                if ch == '\\' {
                                    match self.next() {
                                        Some((_, s)) if s == '\'' => { content.push('\''); continue; }
                                        Some((_, s)) if s == '"' => { content.push('"'); continue; }
                                        Some((_, s)) if s == 'n' => { content.push('\n'); continue; }
                                        Some((_, s)) if s == 'r' => { content.push('\r'); continue; }
                                        Some((_, s)) if s == 't' => { content.push('\t'); continue; }
                                        Some((_, s)) if s == '\\' => { content.push('\\'); continue; }
                                        Some((_, s)) if s == '0' => { content.push('\0'); continue; }
                                        Some((_, s)) if s == 'x' => {
                                            let mut sum = 0;
                                            for _ in 0..2 {
                                                let d = self.next();
                                                if d.is_none_or(|(_, x)| !x.is_ascii_hexdigit()) { 
                                                    self.panic_and_syntax_err_with_help(
                                                        p..p+4, 
                                                        "expected byte escape sequence in the form \\xXX, where X is a hexadecimal digit",
                                                        self.ptr()-1..self.ptr(),
                                                        "this character is the problem"
                                                    ); 
                                                }
                                                sum = sum * 16 + from_hex(d.unwrap().1);
                                            }
                                            content.push(char::from_u32(sum).ok_or_else(|| {
                                                self.panic_and_syntax_err(
                                                    p..p+4, 
                                                    "couldn't decode the invalid byte escape sequence"
                                                ); 
                                            }).unwrap());
                                            continue;
                                        }
                                        Some((_, _)) => {
                                            self.panic_and_syntax_err(
                                                p..p+2, 
                                                "unknown escape, expected one of: \\\', \\\", \\\\, \\n, \\r, \\t, \\0, byte escape \\xXX, or one of unicode escapes \\uXXXX, \\UXXXXXXXX, where X is a hexadecimal digit"
                                            ); 
                                        }
                                        None => {
                                            self.panic_and_syntax_err(
                                                p..p+1, 
                                                "unterminated escape, expected one of: \\\', \\\", \\\\, \\n, \\r, \\t, \0, byte escape \\xXX, or one of unicode escapes \\uXXXX, \\UXXXXXXXX, where X is a hexadecimal digit"
                                            ); 
                                        }
                                    }
                                }

                                // Handle string ending before end of line when the new line is not escaped (string continue)
                                if ch == '\n' && !is_multiline {
                                    self.panic_and_syntax_err_with_suggestions(
                                        begin_p..self.ptr(),
                                        "string literal was not ended before end of line",
                                        &[(self.ptr()-1, parse_until_str, "end the string"),
                                        (self.ptr()-1, "\\", "... or use line continuation to extend the string on the next line")]
                                    );
                                }
                            }
                            content.push(ch);
                        }
                        _ => {                            
                            self.panic_and_syntax_err_with_suggestions(
                                begin_p..self.ptr(),
                                "string literal was not ended",
                                &[(self.ptr(), parse_until_str, "end the string")]
                            );
                        }
                    }
                }

                let end_p = self.ptr();
                self.match_sequence_expect_and_eat(parse_until_str);

                let mut suffix = "";
                if is_ident(self.peek_cp().unwrap_or_default().1, true) {
                    (suffix, _) = self.expect_and_eat_ident();
                }

                return Some(self.new_token(TokenValue::String(StringLiteral {
                    is_raw: is_raw,
                    is_byte: is_byte,
                    begin: &self.source[begin_p..begin_p+offset+1],
                    end: &self.source[end_p..end_p+parse_until_str.len()],
                    content: if is_byte {
                        StringLiteralType::Bytes(content.into_bytes())
                    } else {
                        StringLiteralType::String(content)
                    },
                    suffix: suffix,
                }), begin_p..self.ptr()));
            }
            _ => { return None; }
        }
    }

    fn next_token(&mut self) -> Option<&'a Token<'a>> {
        let p = self.ptr();
        match self.peek() {
            Some(b'\n') => Some(self.new_token_and_advance(TokenValue::NewLine, p..p+1)), // Handle new line separate from white space

            // Handle line continuation as just white space
            Some(b'\\') if self.peek_nth_is(1, b'\n') => Some(self.new_token_and_advance(TokenValue::WhiteSpace, p..p+2)),

            Some(b'(') => Some(self.new_token_and_advance(TokenValue::OpenBracket, p..p+1)),
            Some(b')') => Some(self.new_token_and_advance(TokenValue::ClosedBracket, p..p+1)),
            Some(b'[') => Some(self.new_token_and_advance(TokenValue::OpenSquareBracket, p..p+1)),
            Some(b']') => Some(self.new_token_and_advance(TokenValue::ClosedSquareBracket, p..p+1)),
            Some(b'{') => Some(self.new_token_and_advance(TokenValue::OpenCurlyBracket, p..p+1)),
            Some(b'}') => Some(self.new_token_and_advance(TokenValue::ClosedCurlyBracket, p..p+1)),

            Some(b'.') => { 
                if self.peek_nth_is(1, b'.') {
                    if self.peek_nth_is(2, b'.') {
                        Some(self.new_token_and_advance(TokenValue::Ellipsis, p..p+3))
                    } else {
                        Some(self.new_token_and_advance(TokenValue::DotDot, p..p+2))
                    }
                } else if self.peek_nth(1).take_if(|x| x.is_ascii_digit()).is_some() {
                    // TODO Eat number
                    None
                } else {
                    Some(self.new_token_and_advance(TokenValue::Dot, p..p+1))
                }
            }

            Some(b'=') => { 
                if self.peek_nth_is(1, b'>') {
                    Some(self.new_token_and_advance(TokenValue::ThickArrow, p..p+2))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::EqualEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Equal, p..p+1))
                }
            }

            Some(b'!') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::NotEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Not, p..p+1))
                }
            }

            Some(b'|') => { 
                if self.peek_nth_is(1, b'|') {
                    Some(self.new_token_and_advance(TokenValue::Or, p..p+2))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::BitwiseOrEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::BitwiseOr, p..p+1))
                }
            }

            Some(b'&') => { 
                if self.peek_nth_is(1, b'&') {
                    Some(self.new_token_and_advance(TokenValue::And, p..p+2))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::BitwiseAndEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::BitwiseAnd, p..p+1))
                }
            }

            Some(b':') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::Walrus, p..p+2))
                } else if self.peek_nth_is(1, b':') {
                    Some(self.new_token_and_advance(TokenValue::ColonColon, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Colon, p..p+1))
                }
            }

            Some(b'~') => Some(self.new_token_and_advance(TokenValue::BitwiseNot, p..p+1)),
            Some(b',') => Some(self.new_token_and_advance(TokenValue::Comma, p..p+1)),
            Some(b';') => Some(self.new_token_and_advance(TokenValue::SemiColon, p..p+1)),
            Some(b'$') => Some(self.new_token_and_advance(TokenValue::Dollar, p..p+1)),
            Some(b'?') => Some(self.new_token_and_advance(TokenValue::QuestionMark, p..p+1)),

            Some(b'+') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::PlusEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Plus, p..p+1))
                }
            }

            Some(b'-') => { 
                if self.peek_nth_is(1, b'>') {
                    Some(self.new_token_and_advance(TokenValue::ThinArrow, p..p+2))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::MinusEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Minus, p..p+1))
                }
            }

            Some(b'*') => { 
                if self.peek_nth_is(1, b'*') {
                    if self.peek_nth_is(2, b'*') {
                        Some(self.new_token(TokenValue::PowerEqual, p..p+3))
                    } else {
                        Some(self.new_token_and_advance(TokenValue::Power, p..p+2))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::TimesEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Times, p..p+1))
                }
            }

            Some(b'/') => { 
                if self.peek_nth_is(1, b'*') {
                    return Some(self.eat_multiline_comment());
                } else if self.peek_nth_is(1, b'/') {
                    while !self.peek_nth_is(0, b'\n') { // Eat singleline comment
                        self.advance_cp(1);
                    }
                    return Some(self.new_token(TokenValue::Comment, p..self.ptr()));
                } else if self.peek_nth_is(1, b'_') {
                    if self.peek_nth_is(2, b'=') {
                        Some(self.new_token_and_advance(TokenValue::DivideFloorEqual, p..p+3))
                    } else {
                        Some(self.new_token_and_advance(TokenValue::DivideFloor, p..p+2))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::DivideEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Divide, p..p+1))
                }
            }

            Some(b'%') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::ModEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Mod, p..p+1))
                }
            }

            Some(b'@') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::AtEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::At, p..p+1))
                }
            }

            Some(b'^') => Some(self.new_token(TokenValue::Hat, p..p+1)),

            Some(b'<') => { 
                if self.peek_nth_is(1, b'<') {
                    if self.peek_nth_is(2, b'=') {
                        Some(self.new_token_and_advance(TokenValue::ShiftLeftEqual, p..p+3))
                    } else {
                        Some(self.new_token_and_advance(TokenValue::ShiftLeft, p..p+2))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    if self.peek_nth_is(2, b'>') {
                        Some(self.new_token_and_advance(TokenValue::Spaceship, p..p+3))
                    } else {
                        Some(self.new_token_and_advance(TokenValue::LessOrEqual, p..p+2))
                    }
                } else {
                    Some(self.new_token_and_advance(TokenValue::Less, p..p+1))
                }
            }

            Some(b'>') => { 
                if self.peek_nth_is(1, b'>') {
                    if self.peek_nth_is(2, b'=') {
                        Some(self.new_token_and_advance(TokenValue::ShiftRightEqual, p..p+3))
                    } else {
                        Some(self.new_token_and_advance(TokenValue::ShiftRight, p..p+2))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.new_token_and_advance(TokenValue::GreaterOrEqual, p..p+2))
                } else {
                    Some(self.new_token_and_advance(TokenValue::Greater, p..p+1))
                }
            }

            Some(b'0'..=b'9') => {
                // TODO Eat number
                None
            }

            Some(b'\'' | b'"') => {
                if let Some(string_literal) = self.try_eat_string_literal() {
                    Some(string_literal)
                } else {
                    None
                }
            }

            Some(b'b' | b'r' | b'u') => {
                if let Some(string_literal) = self.try_eat_string_literal() {
                    Some(string_literal)
                } else {
                    if self.match_sequence("break") {
                        Some(self.new_token_and_advance(TokenValue::Break, p..p+5))
                    } else if self.match_sequence("raise") {
                        Some(self.new_token_and_advance(TokenValue::Raise, p..p+5))
                    } else if self.match_sequence("return") {
                        Some(self.new_token_and_advance(TokenValue::Return, p..p+6))
                    } else {
                        None
                    }
                }
            }

            Some(b'#') => { 
                self.advance_bytes(1);
                if is_ident(self.peek_cp().unwrap_or_default().1, true) {
                    self.expect_and_eat_ident();
                    return Some(self.new_token(TokenValue::Directive, p..self.ptr()));
                } else {
                    self.panic_and_syntax_err(p..p+1, "expected identifier after # while parsing compiler directive");
                    None
                }
            }

            // Eat arbitrary continuous unicode white space
            Some(_) if next_code_point(&self.it).take_if(|ch| ch.is_whitespace()).is_some() => {
                while self.peek_cp().take_if(|(_, x)| (x.is_whitespace() && *x != '\n')).is_some() {
                    self.advance_cp(1);
                }
                return Some(self.new_token(TokenValue::WhiteSpace, p..self.ptr()));
            }

            // Eat arbitrary continuous unicode punctuation
            Some(_) if next_code_point(&self.it).take_if(|x| x.general_category_group() == GeneralCategoryGroup::Punctuation).is_some() => {
                while self.peek_cp().take_if(|(_, x)| x.general_category_group() == GeneralCategoryGroup::Punctuation).is_some() {
                    self.advance_cp(1);
                }
                return Some(self.new_token(TokenValue::Punctuation, p..self.ptr()));
            }

            Some(b'T') if self.match_sequence("True") => Some(self.new_token_and_advance(TokenValue::True, p..p+4)),
            Some(b'F') if self.match_sequence("False") => Some(self.new_token_and_advance(TokenValue::False, p..p+5)),
            Some(b'F') if self.match_sequence("First") => Some(self.new_token_and_advance(TokenValue::First, p..p+5)),
            Some(b'L') if self.match_sequence("Last") => Some(self.new_token_and_advance(TokenValue::Last, p..p+4)),

            Some(b'a') if self.match_sequence("and") => Some(self.new_token_and_advance(TokenValue::KeywordAnd, p..p+3)),
            Some(b'o') if self.match_sequence("or") => Some(self.new_token_and_advance(TokenValue::KeywordOr, p..p+2)),
            Some(b'n') if self.match_sequence("not") => Some(self.new_token_and_advance(TokenValue::KeywordNot, p..p+3)),

            Some(b'a') if self.match_sequence("as") => Some(self.new_token_and_advance(TokenValue::As, p..p+2)),
            Some(b'a') if self.match_sequence("assert") => Some(self.new_token_and_advance(TokenValue::Assert, p..p+6)),
            Some(b'a') if self.match_sequence("async") => Some(self.new_token_and_advance(TokenValue::Async, p..p+5)),
            Some(b'a') if self.match_sequence("await") => Some(self.new_token_and_advance(TokenValue::Await, p..p+5)),
                        
            Some(b'c') if self.match_sequence("class") => Some(self.new_token_and_advance(TokenValue::Class, p..p+5)),
            Some(b's') if self.match_sequence("struct") => Some(self.new_token_and_advance(TokenValue::Struct, p..p+6)),
            Some(b'c') if self.match_sequence("continue") => Some(self.new_token_and_advance(TokenValue::Continue, p..p+8)),
            Some(b'd') if self.match_sequence("def") => Some(self.new_token_and_advance(TokenValue::Def, p..p+3)),
            Some(b'd') if self.match_sequence("del") => Some(self.new_token_and_advance(TokenValue::Del, p..p+3)),
            Some(b'e') if self.match_sequence("elif") => Some(self.new_token_and_advance(TokenValue::Elif, p..p+4)),
    
            Some(b'e') if self.match_sequence("else") => Some(self.new_token_and_advance(TokenValue::Else, p..p+4)),
            Some(b'e') if self.match_sequence("except") => Some(self.new_token_and_advance(TokenValue::Except, p..p+6)),
            Some(b'f') if self.match_sequence("finally") => Some(self.new_token_and_advance(TokenValue::Finally, p..p+7)),
            Some(b'f') if self.match_sequence("for") => Some(self.new_token_and_advance(TokenValue::For, p..p+3)),
            Some(b'f') if self.match_sequence("from") => Some(self.new_token_and_advance(TokenValue::From, p..p+4)),
            Some(b'g') if self.match_sequence("global") => Some(self.new_token_and_advance(TokenValue::Global, p..p+6)),
            Some(b'i') if self.match_sequence("if") => Some(self.new_token_and_advance(TokenValue::If, p..p+2)),

            Some(b'i') if self.match_sequence("import") => Some(self.new_token_and_advance(TokenValue::Import, p..p+6)),
            Some(b'i') if self.match_sequence("in") => Some(self.new_token_and_advance(TokenValue::In, p..p+2)),
            Some(b'i') if self.match_sequence("is") => Some(self.new_token_and_advance(TokenValue::Is, p..p+2)),
            Some(b'l') if self.match_sequence("lambda") => Some(self.new_token_and_advance(TokenValue::Lambda, p..p+6)),
            Some(b'n') if self.match_sequence("nonlocal") => Some(self.new_token_and_advance(TokenValue::NonLocal, p..p+8)),
            
            Some(b'p') if self.match_sequence("pass") => Some(self.new_token_and_advance(TokenValue::Pass, p..p+4)),
            Some(b't') if self.match_sequence("try") => Some(self.new_token_and_advance(TokenValue::Try, p..p+3)),
            Some(b'w') if self.match_sequence("while") => Some(self.new_token_and_advance(TokenValue::While, p..p+5)),
            Some(b'w') if self.match_sequence("with") => Some(self.new_token_and_advance(TokenValue::With, p..p+4)),
            Some(b'y') if self.match_sequence("yield") => Some(self.new_token_and_advance(TokenValue::Yield, p..p+5)),

            Some(_) => {
                if let Some(identifier) = self.try_eat_identifier() {
                    Some(identifier)
                } else {
                    self.panic_and_syntax_err(p..(p+1), &format!("unexpected char '{}'", next_code_point(&self.it).unwrap_or_default()));
                    None
                }
                
                // Else: identifier!

                // // Numeric literals (either int or float)
                // if ch.is_digit(10) {
                //     let mut base = 0;
                //     if ch == '0' {
                //         match self.iter.peek_nth(1) {
                //             Some((_, 'b')) | Some((_, 'B')) => { base = 2; }
                //             Some((_, 'o')) | Some((_, 'O')) => { base = 8; } 
                //             Some((_, 'x')) | Some((_, 'X')) => { base = 16; }
                //             Some((_, ch)) if ch.is_whitespace() => {
                //                 return Some(Token {value: TokenValue::Punctuation(punct), loc: self.loc(begin..(it_i+1))});
                //             }
                //             None => {
                //                 return Some(Token {value: TokenValue::Punctuation(punct), loc: self.loc(begin..(it_i+1))});
                //             },
                //             _ => {

                //             }
                //         }

                //         let (_, next) = *self.iter.peek_nth(2).unwrap_or(&(0, ' '));
                //         if base == 2 && !(next == '0' || next == '1') {
                //             self.panic_and_syntax_err(self.loc(it_i..(it_i+2)), &format!("'{}' is not a binary digit, expected after integer base specifier \"0b\"", next));
                //         } else if base == 8 && !(next >= '0' && next <= '7') {
                //             self.panic_and_syntax_err(self.loc(it_i..(it_i+2)), &format!("'{}' is not a octal digit, expected after integer base specifier \"0o\"", next));
                //         } else if base == 16 && !(next.is_ascii_hexdigit() || next == '.') {
                //             self.panic_and_syntax_err(self.loc(it_i..(it_i+2)), &format!("'{}' is not a hexadecimal digit or a dot, expected after numeric base specifier \"0x\"", next));
                //         }
                //         if base != 0 {
                //             self.next(); // Skip 0
                //             self.next(); // Skip base character
                //         }
                //     }
                // }
            }
            None => None
        }
    }    

    fn panic_and_syntax_err(&self, loc: Range<usize>, msg: &str) {
        self.panic_and_syntax_err_with_help_and_suggestions(loc, msg, None, &[]);
    }

    fn panic_and_syntax_err_with_suggestions(&self, loc: Range<usize>, msg: &str, sugggestions: &[(usize, &str, &str)]) {
        self.panic_and_syntax_err_with_help_and_suggestions(loc, msg, None, sugggestions);
    }

    fn panic_and_syntax_err_with_help(&self, loc: Range<usize>, msg: &str, help_loc: Range<usize>, help_msg: &str) {
        self.panic_and_syntax_err_with_help_and_suggestions(loc, msg, Some((help_loc, help_msg)), &[]);
    }

    fn panic_and_syntax_err_with_help_and_suggestions(&self, loc: Range<usize>, msg: &str, help: Option<(Range<usize>, &str)>, sugggestions: &[(usize, &str, &str)]) {
        let mut snippet_err = annotations::Snippet::source(&self.source)
            .line_start(1)
            .fold(true)
            .annotation(
                annotations::Level::Error
                    .span(loc)
                    .label(msg)
            );
            
        if let Some(filename) = &self.filename {
            snippet_err = snippet_err.origin(filename);
        }

        let mut msg_to_render = annotations::Level::Error
            .title("syntax")
            .snippet(snippet_err);

        if let Some((help_loc, help_msg)) = help {
            let help_snippet = annotations::Snippet::source(&self.source)
                .line_start(1)
                .fold(true)
                .annotation(
                    annotations::Level::Error
                        .span(help_loc)
                        .label(help_msg),
                );
            msg_to_render = msg_to_render.snippet(help_snippet);
        }

        let renderer = annotations::Renderer::styled();
        
        let suggestion_color = renderer.stylesheet.suggestion.render();
        let color_len = 1; //format!("{}", suggestion_color).len(); // SIGH.

        let mut edited_sources = Vec::with_capacity(sugggestions.len());
        for (suggestion_location, suggestion, _) in sugggestions {
            let mut source_edited = self.source.to_string();
            source_edited.insert_str(min(max(*suggestion_location, 0), self.source.len()), format!("{}{}{}", suggestion_color, suggestion, renderer.stylesheet.suggestion.render_reset()).as_str());
            edited_sources.push(source_edited);
        }

        if !sugggestions.is_empty() {
            for ((suggestion_location, suggestion, suggestion_message), edited_source) in sugggestions.iter().zip(edited_sources.iter())
            {    
                let suggestion_snippet = annotations::Snippet::source(edited_source)
                    .line_start(1)
                    .fold(true)
                    .annotation(
                        annotations::Level::Suggestion
                            .span((*suggestion_location+color_len)..(*suggestion_location+color_len+suggestion.len()))
                            .label(suggestion_message),
                    );
                msg_to_render = msg_to_render.snippet(suggestion_snippet);
            }
        }
        anstream::println!("{}", renderer.render(msg_to_render));
        panic_for_compiler_error();
    }
}

fn tokenize<'a>(filename: Option<&'a str>, input: &'a str, bump: &'a Bump) -> Vec<&'a Token<'a>> {
    let mut tokenizer: Tokenizer<'a> = Tokenizer::new(filename, input, bump);

    let mut tokens: Vec<&Token<'a>> = Vec::new();
    
    while let Some(token) = tokenizer.next_token() {
        println!("{}:    {:?}", tokens.len() + 1, token);
        tokens.push(token);
    }

    let colors = vec![RgbColor(237, 174, 73), RgbColor(209, 73, 91), RgbColor(0, 121, 140), RgbColor(202, 255, 208)];

    let mut prev_color = None;
    for t in &tokens {
        let mut c = None;
        while c == None || c == prev_color {
            c = Some(colors[rand::thread_rng().gen_range(0..colors.len())]);
        }
        prev_color = c;

        let s = &input[t.code_location.clone()];
        if s.find('\n').is_some() {
            let lines: Vec<_> = s.split('\n').collect();
            for (it, line) in enumerate(&lines) {
                anstream::print!("{}{}{}{}", c.unwrap().render_bg(), AnsiColor::Black.render_fg(), line, Reset.render());
                if it < lines.len() - 1 {
                    anstream::println!();
                }
            }
        } else {
            anstream::print!("{}{}{}{}", c.unwrap().render_bg(), AnsiColor::Black.render_fg(), s, Reset.render());
        }
    }
    anstream::println!("{}", Reset.render());

    return tokens;
}

fn find_first_of<'a>(text: &'a str, patterns: &[&'a str]) -> Option<(usize, &'a str)> {
    patterns.iter()
        .filter_map(|&pat| text.find(pat).map(|idx| (idx, pat)))
        .min_by_key(|&(idx, _)| idx)
}

fn should_wait_for_new_line(input: &String) -> bool {
    if input.ends_with("\\") { return true; }

    // Look for unescaped multiline strings by counting patterns correctly, 
    // especially in cases where, for example ''' is found inside a """ """, 
    // where in this case the ''' shouldn't count as unescaped.
    let mut p = input.as_str();
    loop {
        if let Some((it, pattern)) = find_first_of(p, &["'''", "\"\"\""]) {
            p = &p[it+3..];
            let end_it = p.find(pattern);
            if end_it.is_none() {
                return true;
            } else { 
                p = &p[end_it.unwrap()+3..];
            }
        } else {
            return false;
        }
    }
}

fn main() {
    let args = Args::parse();

    std::env::set_var("RUST_BACKTRACE", "full");

    let bump = Bump::new();
    args.add;

    match args.file {
        Some(file) => {
            match fs::read_to_string(&file) {
                Ok(mut contents) => {
                    contents = contents.trim_start_matches("\u{feff}").to_string().replace("\r\n", "\n"); // Handle BOM and Windows newlines
                    tokenize(Some(&file), &contents, &bump); 
                }
                Err(err) => {
                    println!("{}: {}", &file, err);
                }
            }
        }
        None => {
            println!("Language interpreter");
            println!("Type \"exit()\", Ctrl+C or Ctrl+D to exit.");

            let mut input = String::with_capacity(50);

            let mut rl = DefaultEditor::new().unwrap();
            loop {
                match rl.readline(">>> ") {
                    Ok(line) => {
                        input.clear();

                        let _ = rl.add_history_entry(line.as_str());
                        input.push_str(line.as_str());

                        while should_wait_for_new_line(&input) {
                            match rl.readline("... ") {
                                Ok(l) => {
                                    let _ = rl.add_history_entry(l.as_str());
                                    input.push('\n');
                                    input.push_str(l.as_str());
                                }
                                _ => {
                                    break;
                                }
                            }
                        }

                        if input.trim_end() == "exit()" {
                            break;
                        } 

                        input = input.replace("\r\n", "\n"); // Handle Windows newlines
    
                        let old_panic_hook = take_hook();
                        let mut _result = panic::catch_unwind(|| { 
                            /*
                            let mut tokenizer = Tokenizer::new(None, &input);
                            while let Some((_, ch)) = tokenizer.next() {
                                println!("{}", ch);
                            }
                            */
                            tokenize(None, &input, &bump); 
                        });
                        set_hook(old_panic_hook);

                        // if result.is_ok() { result = panic::catch_unwind(|| { parse(&input); }); }
                        // if result.is_ok() { result = panic::catch_unwind(|| { emit_intermediate_language(&input); }); }
                        // if result.is_ok() { panic::catch_unwind(|| { run(&input); }); }
                    },
                    Err(ReadlineError::Interrupted) => { break },
                    Err(ReadlineError::Eof) => { break },
                    Err(err) => {
                        println!("error, couldn't read input: {:?}", err);
                        break
                    }
                }
            }
        }
    }
}
