use core::str;
use std::panic;
use std::ops::Range;

use bumpalo::{BumpSync, Herd};
use lazy_static::lazy_static;
use rug::ops::Pow;
use thread_local::ThreadLocal;
use unicode_properties::{GeneralCategoryGroup, UnicodeGeneralCategory};

use crate::annotations::Level;
use crate::parse::syntax_err::SyntaxErr;
use crate::parse::token::*;

use super::{SyntaxErrRef, KEYWORDS, STRING_ARENA};

pub type ArenaRef = &'static BumpSync<'static>;

lazy_static! {
    pub static ref TOKEN_ARENA_HERD: Herd = Herd::new();
    pub static ref TOKEN_ARENA: ThreadLocal<BumpSync<'static>> = ThreadLocal::new();

    pub static ref PARSER_ARENA_HERD: Herd = Herd::new();
    pub static ref PARSER_ARENA: ThreadLocal<BumpSync<'static>> = ThreadLocal::new();
}

pub type TokensVec = Vec<Token, &'static BumpSync<'static>>;

pub struct Tokenizer {
    pub filename: Option<String>,
    pub source: &'static str,

    bytes: &'static [u8],

    it: usize, // Byte iterator

    parser_arena: ArenaRef,
    tokens: TokensVec,

    leading_whitespace: usize // Gets consumed into the next non white space token 
}

impl Tokenizer {
    pub fn new(filename: Option<String>, input: &'static str) -> Self {
        let approximate_token_count: usize = input.len() / 3; // Assume 3 bytes per token as estimate

        let token_arena = TOKEN_ARENA.get_or(|| TOKEN_ARENA_HERD.get());
        Self { 
            filename,
            source: input,
            bytes: input.as_bytes(),
            it: 0,
            tokens: Vec::with_capacity_in(approximate_token_count, token_arena),
            parser_arena: PARSER_ARENA.get_or(|| PARSER_ARENA_HERD.get()),
            leading_whitespace: 0
        }
    }

    pub fn collect(mut self) -> Result<TokensVec, SyntaxErrRef> {
        while self.it < self.bytes.len() { 
            self.next_token()?;
        }
        Ok(self.tokens)
    }

    fn parse_string_literal(&mut self) -> Result<Option<StringLiteralRef>, SyntaxErrRef> {
        if let Some(ch) = self.peek() {
            let begin_p = self.it;

            let (mut is_byte, mut is_raw, mut is_unicode) = (false, false, false);
            let mut begin_offset = 0;

            if ch.is_ascii_alphabetic() {
                while !is_raw || !is_byte {
                    match self.peek_nth(begin_offset) {
                        Some(b'b' | b'B') if !is_byte => is_byte = true,
                        Some(b'r' | b'R') if !is_raw => is_raw = true,
                        Some(b'u' | b'U') if !is_unicode => is_unicode = true, // Skip unicode specifier, as strings are unicode by default anyway
                        _ => break
                    }
                    begin_offset += 1;
                }
            }

            // Parse a number of hashes for a raw string, to build the expected terminating sequence.
            let mut parse_until_vec = Vec::<u8, _>::new_in(self.parser_arena); // Since we're allocating in the arena the string can grow without copying
            if is_raw {
                while self.peek_nth_is(begin_offset,  b'#') {
                    parse_until_vec.push(b'#');
                    begin_offset += 1;
                }
            }

            // Expect quote, otherwise return None. Don't throw an error since we're just tip-toeing to see if
            // it's a valid string literal, and not necessarily expecting one. Outside of this function the code 
            // probably starts testing for an identifier.
            //
            // Note: also important to note that by now we haven't advanced any bytes, 
            // we've just been peaking.
            let q = self.peek_nth(begin_offset);
            if !matches!(q, Some(b'\'' | b'\"')) {
                return Ok(None);
            }

            let mut is_multiline = false;
            if self.match_sequence("\"\"\"") {
                is_multiline = true;
                for _ in 0..3 { parse_until_vec.insert(0, b'"'); }
            } else if self.match_sequence("'''") {
                is_multiline = true;
                for _ in 0..3 { parse_until_vec.insert(0, b'\''); }
            } else {
                parse_until_vec.insert(0, q.unwrap()); // We checked above, we're sure there's a quote
            };

            begin_offset += if is_multiline { 3 } else { 1 };
            self.advance(begin_offset); // So far we've just parsed ASCII characters
            
            if !is_multiline {
                is_multiline = is_raw;
            }

            let parse_until = str::from_utf8(&parse_until_vec).expect("internal error; the built string literal ending was not valid utf8");

            let mut cp_buf = [0; 4];

            //
            // At the end we copy to put to the string table.
            //
            // Note that in order to do deduplication we have to allocate the string beforehand somewhere,
            // so it can be checked if it already exists in the string table. If we just push strings the string table 
            // arena and do deduplication later, then at that time we'd have to drop and copy all the non-repeating ones anyway.
            // In any case a copy has to happen. 
            let mut content = Vec::<u8, _>::new_in(self.parser_arena); // Since we're allocating in the arena the string can grow without copying

            while !self.match_sequence(parse_until) {
                let p = self.it;

                match self.next() {
                    Some(ch) => {
                        if !is_raw {
                            // Handle string continue, i.e. escaping newline
                            if matches!((ch, self.peek()), ('\\', Some(b'\n'))) {
                                self.advance(1);
                                continue;
                            }
                            
                            // Handle string ending before end of line when the new line is not escaped (string continue)
                            if ch == '\n' && !is_multiline {
                                return Err(self.syntax_err().loc_msg(begin_p..self.it, "string literal was not ended before end of line")
                                    .suggestion(self.it-1, parse_until, "end the string")
                                    .suggestion(self.it-1, "\\", "... or use line continuation to extend the string on the next line")
                                );
                            }

                            // Handle unicode sequence
                            if matches!((ch, self.peek()), ('\\', Some(b)) if b.eq_ignore_ascii_case(&b'u')) {
                                let mut num_digits = 8; // 8 for 'U'
                                if let Some('u') = self.next() {
                                    num_digits = 4; // 4 for 'u'
                                }
            
                                let mut sum = 0;
                                for _ in 0..num_digits {
                                    match self.peek() {
                                        Some(b) if b.is_ascii_hexdigit() => {
                                            sum = sum * 16 + from_hex(b);
                                            self.advance(1);
                                        }
                                        _ => {
                                            return Err(self.syntax_err().loc_msg(
                                                    p..p+2+num_digits, 
                                                    "expected unicode escape sequence in the form \\uXXXX or \\UXXXXXXXX, where X is a hexadecimal digit"
                                                ).help(self.it..self.it+1, "this character should be a hex digit"),
                                            );
                                        }
                                    }
                                }
                                if let Some(c) = char::from_u32(sum) {
                                    content.extend_from_slice(char::encode_utf8(c, &mut cp_buf).as_bytes());
                                } else {
                                    return Err(self.syntax_err().loc_msg(
                                        p..p+2+num_digits, 
                                        "couldn't decode the invalid unicode escape sequence"
                                    )); 
                                }
                                continue;
                            }

                            // Handle other escapes
                            if ch == '\\' {
                                match self.next() {
                                    Some('\'') => { content.push(b'\''); continue; }
                                    Some('"') => { content.push(b'"'); continue; }
                                    Some('n') => { content.push(b'\n'); continue; }
                                    Some('r') => { content.push(b'\r'); continue; }
                                    Some('t') => { content.push(b'\t'); continue; }
                                    Some('\\') => { content.push(b'\\'); continue; }
                                    Some('0') => { content.push(b'\0'); continue; }
                                    Some('x') => {
                                        let mut sum = 0;
                                        for _ in 0..2 {

                                            match self.peek() {
                                                Some(b) if b.is_ascii_hexdigit() => {
                                                    sum = sum * 16 + from_hex(b);
                                                    self.advance(1);
                                                }
                                                _ => {
                                                    return Err(self.syntax_err().loc_msg(
                                                            p..p+4, 
                                                            "expected byte escape sequence in the form \\xXX, where X is a hexadecimal digit",
                                                        ).help(self.it..self.it+1, "this character should be a hex digit")
                                                    ); 
                                                }
                                            }
                                        }
                                        if let Some(c) = char::from_u32(sum) {
                                            content.extend_from_slice(char::encode_utf8(c, &mut cp_buf).as_bytes());
                                        } else {
                                            return Err(self.syntax_err().loc_msg(
                                                p..p+4, 
                                                "couldn't decode the invalid byte escape sequence"
                                            )); 
                                        }
                                        continue;
                                    }
                                    Some(_) => {
                                        return Err(self.syntax_err().loc_msg(
                                            p..p+2, 
                                            "unknown escape, expected one of: \\\', \\\", \\\\, \\n, \\r, \\t, \\0, byte escape \\xXX, or one of unicode escapes \\uXXXX, \\UXXXXXXXX, where X is a hexadecimal digit"
                                        ));
                                    }
                                    None => {
                                        return Err(self.syntax_err().loc_msg(
                                            p..p+1, 
                                            "unterminated escape, expected one of: \\\', \\\", \\\\, \\n, \\r, \\t, \0, byte escape \\xXX, or one of unicode escapes \\uXXXX, \\UXXXXXXXX, where X is a hexadecimal digit"
                                        ));
                                    }
                                }
                            }
                        }
                        content.extend_from_slice(char::encode_utf8(ch, &mut cp_buf).as_bytes());
                    }
                    _ => {                            
                        return Err(self.syntax_err().loc_msg(
                               begin_p..self.it,
                                "string literal was not ended",
                            ).suggestion(self.it, parse_until, "end the string")
                            .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(is_multiline)
                        );
                    }
                }
            }

            let end_p = self.match_sequence_expect_and_eat(parse_until)?;

            let mut suffix = None;
            if matches!(self.peek_cp(), Some(c) if is_ident(c, true)) {
                let range = self.expect_and_eat_ident_range();
                suffix = Some(self.atom(&self.source[range]))
            }

            let atom = self.atom(unsafe { str::from_utf8_unchecked(&content) });
            let literal = self.parser_arena.alloc(StringLiteral {
                code_location: begin_p..self.it,
                begin_quote: begin_p..begin_p+begin_offset,
                end_quote: end_p..end_p+parse_until.len(),
                is_byte_string: is_byte,
                content: atom,
                suffix,
            });
            Ok(Some(literal))
        } else {
            Ok(None)
        }
    }

    fn parse_numeric_literal(&mut self) -> Result<NumericLiteralRef, SyntaxErrRef> {
        let first = self.peek().take_if(|x| x.is_ascii_digit() || *x == b'.').unwrap_or_default();
        
        if first == 0 {
            return Err(self.syntax_err().loc_msg(self.it..self.it+1, "invalid start of number, must be 0-9 or ."));
        }

        let begin_p = self.it;

        // Figure out base and strip prefix base, if it exists
        let (end_base, base) = match (first, self.peek_nth(1)) {
            (b'0', Some(b'b' | b'B')) => (2, 2),
            (b'0', Some(b'o' | b'O')) => (2, 8),
            (b'0', Some(b'x' | b'X')) => (2, 16),

            // Everything else is treated as decimal.
            _ => (0, 10),
        };
        self.advance(end_base);

        let mut leading_zeros = 0;
        let mut seen_nonzero = false;
        let mut last_underscore = false;

        let mut seen_digit = false;
        while let Some(byte) = self.peek() {
            if is_digit(byte, base) {
                if byte != b'_' { 
                    seen_digit = true;
                    last_underscore = false;
                    if byte != b'0' { seen_nonzero = true; }
                } else {
                    last_underscore = true;
                }
                if byte == b'0' && !seen_nonzero {
                    leading_zeros += 1;
                }
                self.advance(1);
            } else {
                break;
            }
        }
        let end_integer_part = self.it;

        if last_underscore {
            return Err(self.syntax_err()
                .loc_msg(end_integer_part-1..end_integer_part, "integer part of a number can't end with _, _ can be used as a digit separator in other places though")
                .suggestion_replace(end_integer_part-1..end_integer_part, "", "remove the underscore")
            );
        }

        if !seen_digit && !matches!(self.peek(), Some(b'.')){ 
            if end_base != 0 {
                return Err(self.syntax_err()
                    .loc_msg(begin_p+2..end_integer_part, "no digits found in a numeric literal")
                    .annotation(Level::Info, begin_p..begin_p+2, &format!("prefix for base {}", base), true)
                );
            } else {
                return Err(self.syntax_err()
                    .loc_msg(begin_p..end_integer_part, "no digits found in a numeric literal")
                );
            }
        }

        last_underscore = false;

        // Optional fractional part
        let end_fractional_part = if matches!(self.peek(), Some(b'.')) {
            if base != 10 {
                return Err(self.syntax_err()
                    .loc_msg(self.it..self.it+1, "numbers in this base can't have a fractional part")
                    .annotation(Level::Info, begin_p..begin_p+2, &format!("prefix for base {}", base), true)
                );
            }

            self.advance(1);
            if self.peek() == Some(b'_') {
                return Err(self.syntax_err()
                    .loc_msg(self.it..self.it+1, "fractional part of a number can't start with _, _ can be used as a digit separator in other places though")
                    .suggestion_replace(self.it..self.it+1, "", "remove the underscore")
                );
            }

            while let Some(byte) = self.peek() {
                if is_digit(byte, base) { 
                    last_underscore = byte == b'_'; 
                    self.advance(1);
                } 
                else {
                    break;
                }
            }

            if last_underscore {
                return Err(self.syntax_err()
                    .loc_msg(self.it-1..self.it, "fractional part of a number can't end with _, _ can be used as a digit separator in other places though")
                    .suggestion_replace(self.it-1..self.it, "", "remove the underscore")
                );
            }

            self.it
        } else {
            end_integer_part
        };

        last_underscore = false;

        // Optional exponent part
        let end_number_part = if matches!(self.peek(), Some(b'e' | b'E')) {
            self.advance(1);
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.advance(1);
            }
            
            if self.peek() == Some(b'_') {
                return Err(self.syntax_err()
                    .loc_msg(self.it..self.it+1, "exponent of a number in scientific notation can't start with _, _ can be used as a digit separator in other places though"
                    )
                    .suggestion_replace(self.it..self.it+1, "", "remove the underscore")
                );
            }

            let e_begin = self.it;
            
            while let Some(byte) = self.peek() {
                if is_digit(byte, base) { 
                    last_underscore = byte == b'_'; 
                    self.advance(1);
                } 
                else {
                    break;
                }
            }

            if last_underscore {
                return Err(self.syntax_err()
                    .loc_msg(self.it-1..self.it, "exponent of a number in scientific notation can't end with _, _ can be used as a digit separator in other places though")
                    .suggestion_replace(self.it-1..self.it, "", "remove the underscore")
                );
            }

            if self.it == e_begin {
                return Err(self.syntax_err()
                    .loc_msg(e_begin..e_begin+2, "number in scientific notation doesn't have digits in the exponent")
                );
            }
            self.it
        } else {
            end_fractional_part
        };

        if end_integer_part == end_number_part {
            // If an integer and not composed of only zeros and has leading zeros
            if seen_nonzero && leading_zeros > 0 {
                return Err(self.syntax_err()
                    .loc_msg(begin_p+leading_zeros..end_number_part, "it's ambigious if this is meant as a base 8 or base 10 integer")
                    .annotation(Level::Info, begin_p..begin_p+leading_zeros, "... thus leading zeros in integer literals are not permitted", true)
                    .suggestion(begin_p+1, "o", "use a prefix to signify base 8 integers")
                );
            }
        }
        
        let mut suffix = None;
        if matches!(self.peek_cp(), Some(c) if is_ident(c, true)) {
            let range = self.expect_and_eat_ident_range();
            let str = &self.source[range];
            if str == "_" {
                return Err(self.syntax_err()
                    .loc_msg(end_number_part..end_number_part+1, "numeric literal can't end with an _, it's ambigious if this is meant as a digit separator or a suffix")
                    .suggestion_replace(end_number_part..end_number_part+1, " ", "remove the underscore")
                );
            }
            suffix = Some(self.atom(str))
        }

        // @Speed This should be parsed later during type-checking since right now there's no way to know which size it is.
        
        let value = if end_fractional_part != end_number_part {
            Number::Float(Float::Big(rug::Float::with_val(200, rug::Float::parse(&self.source[begin_p..end_number_part]).unwrap())))
        } else if end_integer_part != end_fractional_part {
            let integer_str = &self.source[begin_p..end_integer_part];
            let integer = if integer_str.len() == 0 {
                rug::Rational::from((0, 1))
            } else {
                rug::Rational::from_str_radix(integer_str, base as i32).unwrap()
            };
            
            let fractional_str: &str = &self.source[end_integer_part+1..end_number_part];
            let fractional = if fractional_str.len() == 0 {
                rug::Integer::from(0)
            } else {
                rug::Integer::from_str_radix(fractional_str, base as i32).unwrap()
            };

            let denominator = rug::Integer::from(10).pow(fractional_str.len() as u32);
            Number::Rational(integer + rug::Rational::from((fractional, denominator)))
        } else {
            Number::Integer(Integer::Big(rug::Integer::from_str_radix(&self.source[begin_p..end_number_part], base as i32).unwrap()))
        };

        Ok(self.parser_arena.alloc(NumericLiteral {
            code_location: begin_p..self.it,
            base: if end_base == 0 { None } else { Some(base) },
            end_integer_part: end_integer_part - begin_p,
            end_fractional_part: end_fractional_part - begin_p,
            end_number_part: end_number_part - begin_p,
            value,
            suffix
        }))
    }

    fn next_token(&mut self) -> Result<(), SyntaxErrRef> {
        let p = self.it;

        macro_rules! match_self_peek {
            (
                $( $byte:literal => $token_value:expr ),* $(,)?            // One-bytes
                $( ; $( $custom_pat:pat => $custom_case:block ),+ )+       // Other matches with Some(..)
            ) => {
                match self.peek() {
                    $( Some($byte) => { Ok(self.eat_byte_and_emit_unchecked($token_value)) } )*
                    $( $($custom_pat => { $custom_case })* )*
                    None => Ok(()),
                }
            };
        }

        match_self_peek! {
            b'\n' => TokenValue::NewLine,
            b'(' => TokenValue::OpenBracket,
            b')' => TokenValue::ClosedBracket,
            b'[' => TokenValue::OpenSquareBracket,
            b']' => TokenValue::ClosedSquareBracket,
            b'{' => TokenValue::OpenCurlyBracket,
            b'}' => TokenValue::ClosedCurlyBracket,
            b'~' => TokenValue::BitwiseNot,
            b',' => TokenValue::Comma,
            b';' => TokenValue::SemiColon,
            b'$' => TokenValue::Dollar,
            b'?' => TokenValue::QuestionMark,
            b'^' => TokenValue::Hat;

            Some(b'.') => { 
                if self.peek_nth_is(1, b'.') {
                    if self.peek_nth_is(2, b'.') {
                        Ok(self.eat_bytes_and_emit_unchecked(3,TokenValue::Ellipsis))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::DotDot))
                    }
                } else if self.peek_nth(1).take_if(|x| x.is_ascii_digit()).is_some() {
                    let numeric_literal = self.parse_numeric_literal()?;
                    Ok(self.new_token(TokenValue::Number(numeric_literal), numeric_literal.code_location.clone()))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Dot))
                }
            },

            Some(b'=') => { 
                if self.peek_nth_is(1, b'>') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::ThickArrow))
                } else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::EqualEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Equal))
                }
            },

            Some(b'!') => { 
                if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::NotEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Not))
                }
            },

            Some(b'|') => { 
                if self.peek_nth_is(1, b'|') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::Or))
                } else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::BitwiseOrEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::BitwiseOr))
                }
            },

            Some(b'&') => { 
                if self.peek_nth_is(1, b'&') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::And))
                } else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::BitwiseAndEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::BitwiseAnd))
                }
            },

            Some(b':') => { 
                if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::Walrus))
                } else if self.peek_nth_is(1, b':') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::ColonColon))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Colon))
                }
            },

            Some(b'+') => { 
                if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::PlusEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Plus))
                }
            },

            Some(b'-') => { 
                if self.peek_nth_is(1, b'>') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::ThinArrow))
                } else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::MinusEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Minus))
                }
            },

            Some(b'*') => { 
                if self.peek_nth_is(1, b'*') {
                    if self.peek_nth_is(2, b'*') {
                        Ok(self.eat_bytes_and_emit_unchecked(3,TokenValue::PowerEqual))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::Power))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::TimesEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Times))
                }
            },

            Some(b'/') => { 
                if self.peek_nth_is(1, b'*') {
                    self.leading_whitespace += self.eat_multiline_comment()?;
                    self.next_token() // Recurse to get next non white token to return
                } else if self.peek_nth_is(1, b'/') {
                    /* while !self.peek_nth_is(0, b'\n') { // Eat singleline comment
                        self.advance(1);
                    }
                    return Ok(self.new_token(TokenValue::Comment, p..self.it))); */
                    if self.peek_nth_is(2, b'=') {
                        Ok(self.eat_bytes_and_emit_unchecked(3, TokenValue::DivideFloorEqual))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::DivideFloor))
                    }
                } /*else if self.peek_nth_is(1, b'_') {
                    if self.peek_nth_is(2, b'=') {
                        Ok(self.eat_bytes_and_emit_unchecked(3, TokenValue::DivideFloorEqual))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2, TokenValue::DivideFloor))
                    }
                }*/ else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::DivideEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Divide))
                }
            },

            Some(b'%') => { 
                if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::ModEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Mod))
                }
            },

            Some(b'@') => { 
                /*if is_ident(self.peek_cp().unwrap_or_default().1, true) {
                    self.expect_and_eat_ident_range();
                    let atom = self.atom(&self.source[p..self.it]);
                    return Ok(self.new_token(TokenValue::Directive(atom), p..self.it)))
                }*/

                if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::AtEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::At))
                }
            },

            Some(b'<') => { 
                if self.peek_nth_is(1, b'<') {
                    if self.peek_nth_is(2, b'=') {
                        Ok(self.eat_bytes_and_emit_unchecked(3,TokenValue::ShiftLeftEqual))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::ShiftLeft))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    if self.peek_nth_is(2, b'>') {
                        Ok(self.eat_bytes_and_emit_unchecked(3,TokenValue::Spaceship))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::LessOrEqual))
                    }
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Less))
                }
            },

            Some(b'>') => { 
                if self.peek_nth_is(1, b'>') {
                    if self.peek_nth_is(2, b'=') {
                        Ok(self.eat_bytes_and_emit_unchecked(3,TokenValue::ShiftRightEqual))
                    } else {
                        Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::ShiftRight))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Ok(self.eat_bytes_and_emit_unchecked(2,TokenValue::GreaterOrEqual))
                } else {
                    Ok(self.eat_byte_and_emit_unchecked(TokenValue::Greater))
                }
            },

            Some(b'#') => { 
                while !self.peek_nth_is(0, b'\n') { // Eat singleline comment
                    self.advance(1);
                }
                self.leading_whitespace += self.it - p;
                self.next_token() // Gotta be the newline

                /*self.advance(1);
                if is_ident(self.peek_cp().unwrap_or_default().1, true) {
                    self.expect_and_eat_ident_range();
                    let atom = self.atom(&self.source[p..self.it]);
                    return Ok(self.new_token(TokenValue::Directive(atom), p..self.it))
                } else {
                    Err(self.syntax_err().loc_msg(p..p+1, "expected identifier after # while parsing compiler directive"))
                }*/
            },

            Some(b'0'..=b'9') => {
                let numeric_literal = self.parse_numeric_literal()?;
                Ok(self.new_token(TokenValue::Number(numeric_literal), numeric_literal.code_location.clone()))
            },

            Some(b'\'' | b'"') => {
                if let Some(string_literal) = self.parse_string_literal()? {
                    Ok(self.new_token(TokenValue::String(string_literal), string_literal.code_location.clone()))
                } else {
                    Err(self.syntax_err().loc_msg(p..p+1, "expected a string literal after quote"))
                }
            },

            Some(b'b' | b'r' | b'u') => {
                if let Some(string_literal) = self.parse_string_literal()? {
                    Ok(self.new_token(TokenValue::String(string_literal), string_literal.code_location.clone()))
                } else {
                    Ok(self.expect_and_eat_ident())
                }
            },

            Some(b'a'..=b'z' | b'A'..=b'Z' | b'_') => { // ASCII idents shortcut
                Ok(self.expect_and_eat_ident())
            },

            Some(_) => {
                if matches!(self.peek_cp(), Some(ch) if ch.is_whitespace()) {
                    self.leading_whitespace += self.eat_white_space();
                    self.next_token() // Recurse to get the next non white space token
                } else if matches!(self.peek_cp(), Some(ch) if ch.general_category_group() == GeneralCategoryGroup::Punctuation) {
                    // Eat arbitrary continuous unicode punctuation
                    while matches!(self.peek_cp(), Some(ch) if ch.general_category_group() == GeneralCategoryGroup::Punctuation) {
                        self.advance_cp(1);
                    }
                    let atom = self.atom(&self.source[p..self.it]);
                    Ok(self.new_token(TokenValue::Punctuation(atom),p..self.it))
                } else {
                    // Eat arbitrary unicode identifiers
                    Ok(self.try_eat_identifier()?)
                }
            }
        }
    }    

    #[inline]
    fn new_token(&mut self, value: TokenValue, range: Range<usize>) {
        let trailing_whitespace = self.eat_white_space();
        self.tokens.push(Token { 
            value, 
            loc: CodeLocation { 
                range, 
                leading_whitespace: self.leading_whitespace,
                trailing_whitespace
            } 
        });
        self.leading_whitespace = 0; // Consumed
    }

    #[inline]
    fn peek_nth(&self, i: usize) -> Option<u8> { if self.it + i < self.bytes.len() { Some(self.bytes[self.it + i]) } else { None } }
    
    #[inline]
    fn peek_nth_is(&self, i: usize, b: u8) -> bool { if self.it + i < self.bytes.len() { self.bytes[self.it + i] == b } else { false } }

    #[inline]
    fn peek(&self) -> Option<u8> { self.peek_nth(0) }

    #[inline]
    fn peek_cp(&self) -> Option<char> {
        if self.it < self.bytes.len() {
            Some(next_code_point(unsafe { self.bytes.as_ptr().add(self.it) }))
        } else {
            None
        }
    }

    #[inline]
    fn next(&mut self) -> Option<char> {
        if let Some(ch) = self.peek_cp() {
            self.it += ch.len_utf8();
            Some(ch)
        } else {
            None
        }
    }

    #[inline]
    fn advance(&mut self, byte_count: usize) { self.it += byte_count }

    #[inline]
    fn advance_cp(&mut self, count: usize) {
        for _ in 0..count {
            if let Some(ch) = self.peek_cp() {
                self.advance(ch.len_utf8());
            } else {
                println!("internal error; tried to advance parse pointer by {} code points here, but failed", count);
                panic!();
            }
        }
    }

    fn eat_white_space(&mut self) -> usize {
        let mut bytes: usize = 0;

        loop {
            // First eat the white space, this will probably be the main case
            while let Some(p) = self.peek() {
                if !p.is_ascii_whitespace() || p == b'\n' {
                    // Check for line cont.
                    if p == b'\\' && self.peek_nth_is(1, b'\n') {
                        bytes += 2;
                        self.advance(2);
                        continue;
                    }
                    break;
                }
                bytes += 1;
                self.advance_cp(1);
            }

            // Handle other unicode white space
            if let Some(ch) = self.peek_cp() {
                if !ch.is_whitespace() {
                    break;
                }
                let len = ch.len_utf8();
                bytes += len;
                self.advance_cp(len);
            } else {
                break;
            }
        }
        bytes
    }
    
    fn match_sequence(&mut self, sequence: &str) -> bool {
        self.source[self.it..].starts_with(sequence)
    }

    // Assumes byte already matches!
    fn eat_byte_and_emit_unchecked(&mut self, value: TokenValue) {
        self.eat_bytes_and_emit_unchecked(1, value)
    }

    // Assumes byte already matches!
    fn eat_bytes_and_emit_unchecked(&mut self, i: usize, value: TokenValue) {
        let p = self.it;
        self.advance(i);
        self.new_token(value, p..p+i)
    }

    // Returns the pointer to the beginning of the sequence that was eaten
    fn match_sequence_expect_and_eat(&mut self, sequence: &str) -> Result<usize, SyntaxErrRef> {
        let p = self.it;
        if !self.match_sequence(sequence) {
            return Err(self.syntax_err().loc_msg(p..p+sequence.len(), &format!("expected \"{}\"", sequence)));
        }
        self.advance(sequence.len());
        Ok(p)
    }

    fn eat_multiline_comment(&mut self) -> Result<usize, SyntaxErrRef> {
        let p = self.match_sequence_expect_and_eat("/*")?;

        let mut did_recurse = false;
        while !self.match_sequence("*/") {
            if self.next().is_none() {
                return Err(self.syntax_err().loc_msg(
                    p..self.source.len(), 
                        if !did_recurse { "multiline comment was not closed" }
                        else { "multiline comment was not closed, in nested multiline comments each one must be closed" }
                    )
                    .suggestion(self.source.len(), "*/", "close the comment")
                    .in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(true)
                );
            }
            if self.match_sequence("/*") {
                did_recurse = true;
                self.eat_multiline_comment()?;
            }
        }
        self.match_sequence_expect_and_eat("*/")?;
        Ok(self.it - p)
    }

    #[inline]
    fn atom(&mut self, s: &str) -> Atom { Atom(STRING_ARENA.lock().unwrap().get_or_intern(s)) }

    fn expect_and_eat_ident_range(&mut self) -> Range<usize> {
        let p = self.it;
        while let Some(ch) = self.peek_cp() {
            if !is_ident(ch, false) { break; }
            self.next();
        }
        p..self.it
    }

    fn expect_and_eat_ident(&mut self) {
        let range = self.expect_and_eat_ident_range();
        let atom = self.atom(&self.source[range.clone()]);
        self.new_token(if KEYWORDS.is_keyword(atom) {
            TokenValue::Keyword(atom)
        } else {
            TokenValue::Identifier(atom)
        }, range)
    }

    fn try_eat_identifier(&mut self) -> Result<(), SyntaxErrRef> {
        let cp = if let Some(cp) = self.peek_cp() {
            cp
        } else {
            return Ok(())
        };

        if is_ident(cp, true) {
            Ok(self.expect_and_eat_ident())
        } else {
            Err(self.syntax_err().loc_msg(self.it..self.it+cp.len_utf8(), &format!("unexpected char '{}'", cp)))
        }
    }

    pub fn syntax_err(&self) -> SyntaxErrRef { PARSER_ARENA.get_or(|| PARSER_ARENA_HERD.get()).alloc(SyntaxErr::new(self.filename.clone(), self.source)) }
}

fn from_hex(c: u8) -> u32 {
    match c {
        b'0'..=b'9' => (c as u32) - (b'0' as u32),
        b'a'..=b'f' => (c as u32) - (b'a' as u32) + 10,
        b'A'..=b'F' => (c as u32) - (b'A' as u32) + 10,
        _ => panic!()
    }
}

fn is_digit(c: u8, base: usize) -> bool {
    match base {
        2 => matches!(c, b'0' | b'1' | b'_'),
        8 => matches!(c, b'0'..=b'7' | b'_'),
        10 => matches!(c, b'0'..=b'9' | b'_'),
        16 => matches!(c, b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_'),
        _ => panic!()
    }
}

fn is_ident(ch: char, first_char: bool) -> bool {
    if first_char {
        ch.is_alphabetic() || ch == '_'
    } else {
        ch.is_alphanumeric() || ch == '_'
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

fn next_code_point(bytes: *const u8) -> char {
    let x = unsafe { *bytes };
    if x < 128 { return unsafe { char::from_u32_unchecked(x as u32) } }

    // Multibyte case follows
    // Decode from a byte combination out of: [[[x y] z] w]
    // NOTE: Performance is sensitive to the exact formulation here
    let init = utf8_first_byte(x, 2);

    let y = unsafe { *bytes.add(1) };
    let mut ch = utf8_acc_cont_byte(init, y);
    if x >= 0xE0 {
        // [[x y z] w] case
        // 5th bit in 0xE0 .. 0xEF is always clear, so `init` is still valid
        let y_z = utf8_acc_cont_byte((y & CONT_MASK) as u32, unsafe { *bytes.add(2) });
        ch = init << 12 | y_z;
        if x >= 0xF0 {
            // [x y z w] case
            // use only the lower 3 bits of `init`
            ch = (init & 7) << 18 | utf8_acc_cont_byte(y_z, unsafe { *bytes.add(3) });
        }
    }
    unsafe { char::from_u32_unchecked(ch) }
}
