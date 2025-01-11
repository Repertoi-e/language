
pub struct Utf8Lossy<'a> {
    bytes: &'a [u8],
}

impl<'a> Utf8Lossy<'a> {
    pub fn from_bytes(bytes: &'a [u8]) -> Utf8Lossy<'a> { Utf8Lossy { bytes } }
    pub fn chunks(&self) -> Utf8LossyChunksIter<'a> { Utf8LossyChunksIter { source: &self.bytes, } }
}

pub struct Utf8LossyChunksIter<'a> {
    source: &'a [u8],
}

pub struct Utf8LossyChunk<'a> {
    // Sequence of valid chars.
    // Can be empty between broken UTF-8 chars.
    pub valid: &'a str,
    // Single broken char, empty if none.
    // Empty iff iterator item is last.
    pub broken: &'a [u8],
}

// https://tools.ietf.org/html/rfc3629
#[rustfmt::skip]
static UTF8_CHAR_WIDTH: [u8; 256] = [
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, // 0x1F
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, // 0x3F
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, // 0x5F
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, // 0x7F
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 0x9F
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 0xBF
0,0,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2, // 0xDF
3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3, // 0xEF
4,4,4,4,4,0,0,0,0,0,0,0,0,0,0,0, // 0xFF
];


#[inline]
pub fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}


impl<'a> Iterator for Utf8LossyChunksIter<'a> {
    type Item = Utf8LossyChunk<'a>;

    fn next(&mut self) -> Option<Utf8LossyChunk<'a>> {
        if self.source.is_empty() {
            return None;
        }

        const TAG_CONT_U8: u8 = 128;
        fn unsafe_get(xs: &[u8], i: usize) -> u8 {
            unsafe { *xs.get_unchecked(i) }
        }
        fn safe_get(xs: &[u8], i: usize) -> u8 {
            if i >= xs.len() {
                0
            } else {
                unsafe_get(xs, i)
            }
        }

        let mut i = 0;
        while i < self.source.len() {
            let i_ = i;

            let byte = unsafe_get(self.source, i);
            i += 1;

            if byte < 128 {
            } else {
                let w = utf8_char_width(byte);

                macro_rules! error {
                    () => {{
                        unsafe {
                            let r = Utf8LossyChunk {
                                valid: std::str::from_utf8_unchecked(&self.source[0..i_]),
                                broken: &self.source[i_..i],
                            };
                            self.source = &self.source[i..];
                            return Some(r);
                        }
                    }};
                }

                match w {
                    2 => {
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                    }
                    3 => {
                        match (byte, safe_get(self.source, i)) {
                            (0xE0, 0xA0..=0xBF) => (),
                            (0xE1..=0xEC, 0x80..=0xBF) => (),
                            (0xED, 0x80..=0x9F) => (),
                            (0xEE..=0xEF, 0x80..=0xBF) => (),
                            _ => {
                                error!();
                            }
                        }
                        i += 1;
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                    }
                    4 => {
                        match (byte, safe_get(self.source, i)) {
                            (0xF0, 0x90..=0xBF) => (),
                            (0xF1..=0xF3, 0x80..=0xBF) => (),
                            (0xF4, 0x80..=0x8F) => (),
                            _ => {
                                error!();
                            }
                        }
                        i += 1;
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                    }
                    _ => {
                        error!();
                    }
                }
            }
        }

        let r = Utf8LossyChunk {
            valid: unsafe { std::str::from_utf8_unchecked(self.source) },
            broken: &[],
        };
        self.source = &[];
        Some(r)
    }
}

pub fn utf8_normalize_newlines_and_remove_bom(buffer: &mut [u8]) -> &mut [u8] {
    let buffer = if buffer.starts_with(b"\xEF\xBB\xBF") {
        &mut buffer[3..]
    } else {
        buffer
    };

    let mut write_idx = 0;
    let mut read_idx = 0;
    while read_idx < buffer.len() {
        if buffer[read_idx] == b'\r' && read_idx + 1 < buffer.len() && buffer[read_idx + 1] == b'\n' {
            buffer[write_idx] = b'\n';
            read_idx += 2;
        } else {
            buffer[write_idx] = buffer[read_idx];
            read_idx += 1;
        }
        write_idx += 1;
    }
    &mut buffer[..write_idx]
}
