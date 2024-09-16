use bumpalo::Bump;

use std::panic;
use std::ops::Range;
use std::cmp::{max, min};

use unicode_properties::{GeneralCategoryGroup, UnicodeGeneralCategory};

use crate::{annotations, StringTable};
use crate::tokenizer::token::*;

pub struct Tokenizer<'a> {
    pub filename: Option<&'a str>,
    pub source: &'a str,

    it: &'a [u8],  // Byte iterator

    arena: &'a Bump,
    string_table: &'a StringTable<'a>,
}

struct Suggestion<'a> {
    location: usize,
    suggestion: &'a str, 
    message: &'a str,
    replacement_range: Option<Range<usize>>,
}

impl<'a> Suggestion<'a> {
    pub fn new(location: usize, suggestion: &'a str, message: &'a str) -> Self {
        Self {
            location: location,
            suggestion: suggestion,
            message: message,
            replacement_range: None
        }
    }

    pub fn new_replace(replacement_range: Range<usize>, suggestion: &'a str, message: &'a str) -> Self {
        Self {
            location: 0,
            suggestion: suggestion,
            message: message,
            replacement_range: Some(replacement_range)
        }
    }
}

impl<'a> Tokenizer<'a> {
    pub fn new(filename: Option<&'a str>, input: &'a str, arena: &'a Bump, string_table: &'a StringTable<'a>) -> Self {
        Self { 
            filename: filename,
            source: input,
            it: input.as_bytes(),
            arena: arena,
            string_table: string_table,
        }
    }

    pub fn next_token(&mut self) -> Option<&'a Token<'a>> {
        let p = self.ptr();

        macro_rules! match_self_peek {
            (
                $( $byte:literal => $token_value:expr ),* $(,)?                                                          // One-bytes
                $( ; )+
                $( ($keyword_byte:literal, $keyword_expr:expr, $keyword_token_value:expr) ),* $(,)?                      // Keywords
                $( ; $( $custom_pat:pat => $custom_case:block ),+ )+                                                     // Other matches with Some(..)
            ) => {
                match self.peek() {
                    $( Some($byte) => { Some(self.eat_byte_and_emit_unchecked($token_value)) } )*
                    $( Some($keyword_byte) if self.match_sequence($keyword_expr) => { Some(self.eat_sequence_and_emit_unchecked($keyword_expr, $keyword_token_value)) } )*
                    $( $($custom_pat => { $custom_case })* )*
                    None => None,
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
            b'^' => TokenValue::Hat
            
            ;

            (b'T', "True", TokenValue::True),
            (b'F', "False", TokenValue::False),
            (b'F', "First", TokenValue::First),
            (b'L', "Last", TokenValue::Last),
    
            (b'a', "and", TokenValue::KeywordAnd),
            (b'o', "or", TokenValue::KeywordOr),
            (b'n', "not", TokenValue::KeywordNot),
    
            (b'a', "as", TokenValue::As),
            (b'a', "assert", TokenValue::Assert),
            (b'a', "async", TokenValue::Async),
            (b'a', "await", TokenValue::Await),
    
            (b'c', "class", TokenValue::Class),
            (b's', "struct", TokenValue::Struct),
            (b'c', "continue", TokenValue::Continue),
            (b'd', "def", TokenValue::Def),
            (b'd', "del", TokenValue::Del),
            (b'e', "elif", TokenValue::Elif),
    
            (b'e', "else", TokenValue::Else),
            (b'e', "except", TokenValue::Except),
            (b'f', "finally", TokenValue::Finally),
            (b'f', "for", TokenValue::For),
            (b'f', "from", TokenValue::From),
            (b'g', "global", TokenValue::Global),
            (b'i', "if", TokenValue::If),
    
            (b'i', "import", TokenValue::Import),
            (b'i', "in", TokenValue::In),
            (b'i', "is", TokenValue::Is),
            (b'l', "lambda", TokenValue::Lambda),
            (b'n', "nonlocal", TokenValue::NonLocal),
    
            (b'p', "pass", TokenValue::Pass),
            (b't', "try", TokenValue::Try),
            (b'w', "while", TokenValue::While),
            (b'w', "with", TokenValue::With),
            (b'y', "yield", TokenValue::Yield),

            ;
                        
            Some(b'.') => { 
                if self.peek_nth_is(1, b'.') {
                    if self.peek_nth_is(2, b'.') {
                        Some(self.eat_bytes_and_emit_unchecked(3, TokenValue::Ellipsis))
                    } else {
                        Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::DotDot))
                    }
                } else if self.peek_nth(1).take_if(|x| x.is_ascii_digit()).is_some() {
                    Some(self.expect_and_eat_number())
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Dot))
                }
            },

            Some(b'=') => { 
                if self.peek_nth_is(1, b'>') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::ThickArrow))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::EqualEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Equal))
                }
            },

            Some(b'!') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::NotEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Not))
                }
            },

            Some(b'|') => { 
                if self.peek_nth_is(1, b'|') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::Or))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::BitwiseOrEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::BitwiseOr))
                }
            },

            Some(b'&') => { 
                if self.peek_nth_is(1, b'&') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::And))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::BitwiseAndEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::BitwiseAnd))
                }
            },

            Some(b':') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::Walrus))
                } else if self.peek_nth_is(1, b':') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::ColonColon))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Colon))
                }
            },

            Some(b'+') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::PlusEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Plus))
                }
            },

            Some(b'-') => { 
                if self.peek_nth_is(1, b'>') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::ThinArrow))
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::MinusEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Minus))
                }
            },

            Some(b'*') => { 
                if self.peek_nth_is(1, b'*') {
                    if self.peek_nth_is(2, b'*') {
                        Some(self.eat_bytes_and_emit_unchecked(3, TokenValue::PowerEqual))
                    } else {
                        Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::Power))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::TimesEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Times))
                }
            },

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
                        Some(self.eat_bytes_and_emit_unchecked(3, TokenValue::DivideFloorEqual))
                    } else {
                        Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::DivideFloor))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::DivideEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Divide))
                }
            },

            Some(b'%') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::ModEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Mod))
                }
            },

            Some(b'@') => { 
                if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::AtEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::At))
                }
            },

            Some(b'<') => { 
                if self.peek_nth_is(1, b'<') {
                    if self.peek_nth_is(2, b'=') {
                        Some(self.eat_bytes_and_emit_unchecked(3, TokenValue::ShiftLeftEqual))
                    } else {
                        Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::ShiftLeft))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    if self.peek_nth_is(2, b'>') {
                        Some(self.eat_bytes_and_emit_unchecked(3, TokenValue::Spaceship))
                    } else {
                        Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::LessOrEqual))
                    }
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Less))
                }
            },

            Some(b'>') => { 
                if self.peek_nth_is(1, b'>') {
                    if self.peek_nth_is(2, b'=') {
                        Some(self.eat_bytes_and_emit_unchecked(3, TokenValue::ShiftRightEqual))
                    } else {
                        Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::ShiftRight))
                    }
                } else if self.peek_nth_is(1, b'=') {
                    Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::GreaterOrEqual))
                } else {
                    Some(self.eat_byte_and_emit_unchecked(TokenValue::Greater))
                }
            },

            Some(b'0'..=b'9') => {
                Some(self.expect_and_eat_number())
            },

            Some(b'\'' | b'"') => {
                if let Some(string_literal) = self.try_eat_string_literal() {
                    Some(string_literal)
                } else {
                    self.panic_and_syntax_err(p..p+1, "expected a string literal after quote");
                    None
                }
            },

            Some(b'b' | b'r' | b'u') => {
                if let Some(string_literal) = self.try_eat_string_literal() {
                    Some(string_literal)
                } else {
                    if self.match_sequence("break") {
                        Some(self.eat_sequence_and_emit_unchecked("break", TokenValue::Break))
                    } else if self.match_sequence("raise") {
                        Some(self.eat_sequence_and_emit_unchecked("raise", TokenValue::Raise))
                    } else if self.match_sequence("return") {
                        Some(self.eat_sequence_and_emit_unchecked("return", TokenValue::Return))
                    } else {
                        self.try_eat_identifier()
                    }
                }
            },

            Some(b'#') => { 
                self.advance_bytes(1);
                if is_ident(self.peek_cp().unwrap_or_default().1, true) {
                    self.expect_and_eat_ident();
                    return Some(self.new_token(TokenValue::Directive, p..self.ptr()));
                } else {
                    self.panic_and_syntax_err(p..p+1, "expected identifier after # while parsing compiler directive");
                    None
                }
            },

            Some(ch) => {
                // Treat line continuation as just white space
                if ch == b'\\' && self.peek_nth_is(1, b'\n') { 
                    return Some(self.eat_bytes_and_emit_unchecked(2, TokenValue::WhiteSpace)) 
                }

                // Eat arbitrary continuous unicode white space
                if next_code_point(&self.it).take_if(|ch| ch.is_whitespace()).is_some() {
                    while self.peek_cp().take_if(|(_, x)| (x.is_whitespace() && *x != '\n')).is_some() {
                        self.advance_cp(1);
                    }
                    return Some(self.new_token(TokenValue::WhiteSpace, p..self.ptr()));
                }

                // Eat arbitrary continuous unicode punctuation
                if next_code_point(&self.it).take_if(|x| x.general_category_group() == GeneralCategoryGroup::Punctuation).is_some() {
                    while self.peek_cp().take_if(|(_, x)| x.general_category_group() == GeneralCategoryGroup::Punctuation).is_some() {
                        self.advance_cp(1);
                    }
                    return Some(self.new_token(TokenValue::Punctuation, p..self.ptr()));
                }
            
                if let Some(identifier) = self.try_eat_identifier() {
                    Some(identifier)
                } else {
                    self.panic_and_syntax_err(p..(p+1), &format!("unexpected char '{}'", next_code_point(&self.it).unwrap_or_default()));
                    None
                }
            }
        }
    }    
}

impl<'a> Tokenizer<'a> {
    #[inline]
    fn new_token(&self, value: TokenValue<'a>, range: Range<usize>) -> &'a Token<'a> {
        self.arena.alloc(Token { value: value, code_location: range })
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

    // Assumes sequence already matches!
    fn eat_sequence_and_emit_unchecked(&mut self, sequence: &str, value: TokenValue<'a>) -> &'a Token<'a> {
        let p = self.ptr();
        self.advance_bytes(sequence.len());
        self.new_token(value, p..p+sequence.len())
    }

    // Assumes byte already matches!
    fn eat_byte_and_emit_unchecked(&mut self, value: TokenValue<'a>) -> &'a Token<'a> {
        self.eat_bytes_and_emit_unchecked(1, value)
    }

    // Assumes byte already matches!
    fn eat_bytes_and_emit_unchecked(&mut self, i: usize, value: TokenValue<'a>) -> &'a Token<'a> {
        let p = self.ptr();
        self.advance_bytes(i);
        self.arena.alloc(Token { value: value, code_location: p..p+i })
    }

    // Returns the pointer to the beginning of the sequence that was eaten
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
                    &[Suggestion::new(self.source.len(), "*/", "close the comment")]
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
            let range = self.expect_and_eat_ident();
            Some(self.new_token(TokenValue::Identifier, range))
        } else {
            None
        }
    }
    
    fn expect_and_eat_ident(&mut self) -> Range<usize> {
        if !is_ident(self.peek_cp().unwrap_or_default().1, true) {
            self.panic_and_syntax_err(self.ptr()..self.ptr()+1, "invalid start of identifier, must be an alphabetic character or _");
        }

        let p = self.ptr();
        while self.peek_cp().take_if(|(_, x)| is_ident(*x, false)).is_some() {
            self.next();
        }
        
        p..self.ptr()
    }

    fn expect_and_eat_number(&mut self) -> &'a Token<'a> {
        let first = self.peek().take_if(|x| x.is_ascii_digit() || *x == b'.').unwrap_or_default();
        
        if first == 0 {
            self.panic_and_syntax_err(self.ptr()..self.ptr()+1, "invalid start of number, must be 0-9 or .");
        }

        // Figure out base and strip prefix base, if it exists
        let (end_base, base) = match (first, self.peek_nth(1)) {
            (b'0', Some(b'b' | b'B')) => (2, 2),
            (b'0', Some(b'o' | b'O')) => (2, 8),
            (b'0', Some(b'x' | b'X')) => (2, 16),

            // Everything else is treated as decimal.
            _ => (0, 10),
        };
        self.advance_bytes(end_base);

        let begin_number = self.ptr();
        while self.peek().take_if(|b| match base {
            2 => matches!(b, b'0' | b'1' | b'_'),
            8 => matches!(b, b'0'..=b'7' | b'_'),
            10 => matches!(b, b'0'..=b'9' | b'_'),
            16 => matches!(b, b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_'),
            _ =>  false
        }).is_some() {
            self.advance_bytes(1);
        }

        let end_number = self.ptr();


        // let without_prefix = &input[end_prefix..];
        self.new_token(TokenValue::Number, begin_number..end_number)
    }
    
    fn try_eat_string_literal(&mut self) -> Option<&'a Token<'a>> {
        match self.peek() {
            Some(ch) => {
                let begin_p = self.ptr();

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
                let mut parse_until = bumpalo::collections::String::new_in(&self.arena); // Since we're allocating in the arena the string can grow without copying
                if is_raw {
                    while self.peek_nth_is(begin_offset,  b'#') {
                        parse_until.push('#');
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
                    return None;
                }

                let mut is_multiline = false;
                if self.match_sequence("\"\"\"") {
                    is_multiline = true;
                    parse_until.insert_str(0, "\"\"\"");
                } else if self.match_sequence("'''") {
                    is_multiline = true;
                    parse_until.insert_str(0, "'''");
                } else {
                    parse_until.insert(0, q.unwrap() as char); // We checked above, we're sure there's a quote
                };

                begin_offset += if is_multiline { 3 } else { 1 };
                self.advance_bytes(begin_offset); // So far we've just parsed ASCII characters
               
                if !is_multiline {
                    is_multiline = is_raw;
                }

                //
                // At the end we copy to put to the string table.
                //
                // Note that in order to do deduplication we have to allocate the string beforehand somewhere,
                // so it can be checked if it already exists in the string table. If we just push strings the string table 
                // arena and do deduplication later, then at that time we'd have to drop and copy all the non-repeating ones anyway.
                // In any case a copy has to happen. 
                let mut content = bumpalo::collections::String::new_in(self.arena); // Since we're allocating in the arena the string can grow without copying

                while !self.match_sequence(&parse_until) {
                    match self.next() {
                        Some((p, ch)) => {
                            if !is_raw {
                                // Handle string continue, i.e. escaping newline
                                if matches!((ch, self.peek()), ('\\', Some(b'\n'))) {
                                    self.advance_bytes(1);
                                    continue;
                                }
                                
                                // Handle string ending before end of line when the new line is not escaped (string continue)
                                if ch == '\n' && !is_multiline {
                                    self.panic_and_syntax_err_with_suggestions(
                                        begin_p..self.ptr(),
                                        "string literal was not ended before end of line",
                                        &[Suggestion::new(self.ptr()-1, &parse_until, "end the string"),
                                        Suggestion::new(self.ptr()-1, "\\", "... or use line continuation to extend the string on the next line")]
                                    );
                                }

                                // Handle unicode sequence
                                if matches!((ch, self.peek()), ('\\', Some(b)) if b.eq_ignore_ascii_case(&b'u')) {
                                    let mut num_digits = 8; // 8 for 'U'
                                    if let Some((_, 'u')) = self.next() {
                                        num_digits = 4; // 4 for 'u'
                                    }
                
                                    let mut sum = 0;
                                    for _ in 0..num_digits {
                                        match self.peek() {
                                            Some(b) if b.is_ascii_hexdigit() => {
                                                sum = sum * 16 + from_hex(b);
                                                self.advance_bytes(1);
                                            }
                                            _ => {
                                                self.panic_and_syntax_err_with_help(
                                                    p..p+2+num_digits, 
                                                    "expected unicode escape sequence in the form \\uXXXX or \\UXXXXXXXX, where X is a hexadecimal digit",
                                                    self.ptr()..self.ptr()+1, 
                                                    "this character should be a hex digit"
                                                ); 
                                            }
                                        }
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
                                        Some((_, '\'')) => { content.push('\''); continue; }
                                        Some((_, '"')) => { content.push('"'); continue; }
                                        Some((_, 'n')) => { content.push('\n'); continue; }
                                        Some((_, 'r')) => { content.push('\r'); continue; }
                                        Some((_, 't')) => { content.push('\t'); continue; }
                                        Some((_, '\\')) => { content.push('\\'); continue; }
                                        Some((_, '0')) => { content.push('\0'); continue; }
                                        Some((_, 'x')) => {
                                            let mut sum = 0;
                                            for _ in 0..2 {

                                                match self.peek() {
                                                    Some(b) if b.is_ascii_hexdigit() => {
                                                        sum = sum * 16 + from_hex(b);
                                                        self.advance_bytes(1);
                                                    }
                                                    _ => {
                                                        self.panic_and_syntax_err_with_help(
                                                            p..p+4, 
                                                            "expected byte escape sequence in the form \\xXX, where X is a hexadecimal digit",
                                                            self.ptr()..self.ptr()+1,
                                                            "this character should be a hex digit"
                                                        ); 
                                                    }
                                                }
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
                            }
                            content.push(ch);
                        }
                        _ => {                            
                            self.panic_and_syntax_err_with_suggestions(
                                begin_p..self.ptr(),
                                "string literal was not ended",
                                &[Suggestion::new(self.ptr(), &parse_until, "end the string")]
                            );
                        }
                    }
                }

                let end_p = self.match_sequence_expect_and_eat(&parse_until);

                let mut suffix = None;
                if matches!(self.peek_cp(), Some((_, c)) if is_ident(c, true)) {
                    suffix = Some(self.expect_and_eat_ident());
                }

                return Some(self.new_token(TokenValue::String(StringLiteral {
                    is_raw: is_raw,
                    is_byte: is_byte,
                    begin: begin_p..begin_p+begin_offset,
                    end: end_p..end_p+&parse_until.len(),
                    content: if is_byte {
                        StringLiteralValue::Bytes(self.string_table.get_bytes_or_insert(&content))
                    } else {
                        StringLiteralValue::String(self.string_table.get_string_or_insert(&content))
                    },
                    suffix: suffix,
                }), begin_p..self.ptr()));
            }
            _ => { return None; }
        }
    }

    fn panic_and_syntax_err(&self, loc: Range<usize>, msg: &str) {
        self.panic_and_syntax_err_with_help_and_suggestions(loc, msg, None, &[]);
    }

    fn panic_and_syntax_err_with_suggestions(&self, loc: Range<usize>, msg: &str, suggestions: &[Suggestion]) {
        self.panic_and_syntax_err_with_help_and_suggestions(loc, msg, None, suggestions);
    }

    fn panic_and_syntax_err_with_help(&self, loc: Range<usize>, msg: &str, help_loc: Range<usize>, help_msg: &str) {
        self.panic_and_syntax_err_with_help_and_suggestions(loc, msg, Some((help_loc, help_msg)), &[]);
    }

    fn panic_and_syntax_err_with_help_and_suggestions(&self, loc: Range<usize>, msg: &str, help: Option<(Range<usize>, &str)>, suggestions: &[Suggestion]) {
        let checked_loc = min(max(0, loc.start), self.source.len())..min(max(0, loc.end), self.source.len());
        
        let mut snippet_err = annotations::Snippet::source(&self.source)
            .line_start(1)
            .fold(true)
            .annotation(
                annotations::Level::Error
                    .span(checked_loc)
                    .label(msg)
            );
            
        if let Some(filename) = &self.filename {
            snippet_err = snippet_err.origin(filename);
        }

        let mut msg_to_render = annotations::Level::Error
            .title("syntax")
            .snippet(snippet_err);

        if let Some((help_loc, help_msg)) = help {
            let checked_range = min(max(0, help_loc.start), self.source.len())..min(max(0, help_loc.end), self.source.len());

            let help_snippet = annotations::Snippet::source(&self.source)
                .line_start(1)
                .fold(true)
                .annotation(
                    annotations::Level::Error
                        .span(checked_range)
                        .label(help_msg),
                );
            msg_to_render = msg_to_render.snippet(help_snippet);
        }

        let mut sources = Vec::<(String, usize)>::new();

        let renderer = annotations::Renderer::styled();
        for s in suggestions {
            let mut source_edited = self.source.to_string();

            let formatted = format!("{}{}{}", 
                renderer.stylesheet.suggestion.render(), 
                s.suggestion, 
                renderer.stylesheet.suggestion.render_reset()
            );
            
            let location;
            if let Some(range) = &s.replacement_range {
                let checked_range = min(max(0, range.start), self.source.len())..min(max(0, range.end), self.source.len());

                source_edited.replace_range(checked_range.clone(), formatted.as_str());
                location = checked_range.start;
            } else {
                location = min(max(0, s.location), self.source.len());
                source_edited.insert_str(location, formatted.as_str());
            }
            sources.push((source_edited, location));
        }

        for (i, s) in suggestions.iter().enumerate() {
            let (source, location) = &sources[i];
            msg_to_render = msg_to_render.snippet(annotations::Snippet::source(source.as_str())
                .line_start(1)
                .fold(true)
                .annotation(
                    annotations::Level::Suggestion
                        .span((location+1)..(location+1+s.suggestion.len()))
                        .label(s.message),
                )
            );
        }

        anstream::println!("{}", renderer.render(msg_to_render));
        panic_for_compiler_error();
    }
}

fn panic_for_compiler_error() {
    panic::set_hook(Box::new(|_| {})); // Remove 'thread '...' panicked at ... ' message, since now we're just reporting a compiler error
    panic!();
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
