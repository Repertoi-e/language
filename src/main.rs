use anstyle::{AnsiColor, Reset, RgbColor};
use bumpalo::Bump;
use clap::Parser;

use itertools::enumerate;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use core::str;
use std::collections::HashSet;
use std::panic::{set_hook, take_hook};
use std::{fs, panic};

mod annotations;

mod tokenizer;
use tokenizer::*;

#[derive(Parser, Debug)]
#[command(version = "0.0.1", about = "Interpreter and compiler for a language.", long_about = None)]
struct Args {
    #[arg(help = "The file to start running from.")]
    file: Option<String>,

    #[arg(short, long, default_value = "", help = "Parse and interpret a string before the beginning of the program.")]
    add: String,

    #[arg(short, long, conflicts_with = "file", default_value = "", help = "Runs the provided string as a standalone program.")]
    run: String,
}

fn tokenize<'a>(tokenizer: &mut Tokenizer<'a>) -> Vec<&'a Token<'a>> {
    let mut tokens: Vec<&Token<'a>> = Vec::new();
    
    while let Some(token) = tokenizer.next_token() {
        println!("{}:    {:?}", tokens.len() + 1, token);
        tokens.push(token);
    }

    let colors = vec![RgbColor(237, 174, 73), RgbColor(209, 73, 91), RgbColor(0, 121, 140), RgbColor(202, 255, 208)];

    let mut color = 0;
    for t in &tokens {
        color = (color + 1) % colors.len();

        let c = colors[color];

        let s = &tokenizer.source[t.code_location.clone()];
        if s.find('\n').is_some() {
            let lines: Vec<_> = s.split('\n').collect();
            for (it, line) in enumerate(&lines) {
                anstream::print!("{}{}{}{}", c.render_bg(), AnsiColor::Black.render_fg(), line, Reset.render());
                if it < lines.len() - 1 {
                    anstream::println!();
                }
            }
        } else {
            anstream::print!("{}{}{}{}", c.render_bg(), AnsiColor::Black.render_fg(), s, Reset.render());
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

pub struct StringTable<'string> {
    table: HashSet<&'string [u8]>,
    arena: Bump,
}

impl<'string> StringTable<'string> {
    pub fn new() -> Self {
        Self {
            table: HashSet::new(),
            arena: Bump::new(),
        }
    }

    pub fn get_string_or_insert(&'string self, s: &bumpalo::collections::String) -> &'string str {
        if let Some(&existing) = self.table.get(s.as_bytes()) { unsafe { return str::from_utf8_unchecked(existing); } }
        let allocated = self.arena.alloc_str(&s.as_str());
        allocated
    }

    pub fn get_bytes_or_insert(&'string self, s: &bumpalo::collections::String) -> &'string [u8] {
        if let Some(&existing) = self.table.get(s.as_bytes()) { return existing; }
        let allocated = self.arena.alloc_slice_copy(&s.as_bytes());
        allocated
    }
}

fn main() {
    let args = Args::parse();

    std::env::set_var("RUST_BACKTRACE", "full");

    let string_table = StringTable::new();
    let token_arena = Bump::new();
    
    if !args.add.is_empty() {
        let mut tokenizer = Tokenizer::new(Some("<--add>"), &args.add, &token_arena, &string_table);
        tokenize(&mut tokenizer);
    }
    
    if !args.run.is_empty() {
        let mut tokenizer = Tokenizer::new(Some("<--run>"), &args.run, &token_arena, &string_table);
        tokenize(&mut tokenizer);
        return;
    }

    if let Some(file) = args.file {
        match fs::read_to_string(&file) {
            Ok(mut contents) => {
                contents = contents.trim_start_matches("\u{feff}").to_string().replace("\r\n", "\n"); // Handle BOM and Windows newlines
                
                let mut tokenizer = Tokenizer::new(Some(&file), &contents, &token_arena, &string_table);
                tokenize(&mut tokenizer);
            }
            Err(err) => {
                println!("{}: {}", &file, err);
            }
        }
        return;
    } 
    
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
                    let mut tokenizer = Tokenizer::new(None, &input, &token_arena, &string_table);
                    tokenize(&mut tokenizer);
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
