#![feature(allocator_api)]

use anstyle::{AnsiColor, Reset, RgbColor};
use bucket_array::BucketArray;
use bumpalo::Bump;
use clap::Parser;

use itertools::enumerate;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use string_interner::StringInterner;

use core::str;
use std::collections::HashSet;
use std::fs;

mod annotations;

mod tokenizer;
use tokenizer::*;

mod bucket_array;

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

fn tokenize<'source, 's, 'c>(tokenizer: &mut Tokenizer<'source, 's, 'c>) -> Result<usize, SyntaxError> {
    let mut token_count = 0usize;
    while let Some(_) = tokenizer.next_token()? {
        // println!("{}:    {:?}", tokens.len() + 1, tokenizer.token_bucket_array.get(token).expect(format!("internal error; couldn't get token at index: {}", token).as_str()));
        token_count += 1;
        // tokens.push(token);
    }
    println!("Count: {}", token_count);
    /* 
    let colors = vec![RgbColor(237, 174, 73), RgbColor(209, 73, 91), RgbColor(0, 121, 140), RgbColor(202, 255, 208)];

    let mut color = 0;
    for t_index in &tokens {
        color = (color + 1) % colors.len();

        let c = colors[color];

        let t = tokenizer.token_bucket_array.get(*t_index).expect(format!("internal error; couldn't get token at index: {}", t_index).as_str());

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
    anstream::println!("{}", Reset.render());*/
    return Ok(token_count);
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

    let string_interner = StringInterner::default();
    let st = string_interner.get_or_intern_static("");
    let str: &str = st;

    let token_arena = Bump::new();
    let mut token_bucket_array = BucketArray::new_in(&token_arena);
    
    // Insert dummy token to guarantee bucket indices of actual tokens start from 1. 
    // We do this because TokenIndex is a NonZero which has nice space optimizations for Option<TokenIndex>
    token_bucket_array.push(Token {value: TokenValue::WhiteSpace, code_location: 0..0}); 

    if !args.add.is_empty() {
        let mut tokenizer = Tokenizer::new(Some("<--add>".to_string()), &args.add, &token_arena, &string_table, &mut token_bucket_array);
        if let Err(e) = tokenize(&mut tokenizer) { anstream::println!("{}", e.msg); return; }
    }
    
    if !args.run.is_empty() {
        let mut tokenizer = Tokenizer::new(Some("<--run>".to_string()), &args.run, &token_arena, &string_table, &mut token_bucket_array);
        if let Err(e) = tokenize(&mut tokenizer) { anstream::println!("{}", e.msg); return; }
        return;
    }

    if let Some(file) = args.file {
        match fs::read_to_string(&file) {
            Ok(mut contents) => {
                contents = contents.trim_start_matches("\u{feff}").to_string().replace("\r\n", "\n"); // Handle BOM and Windows newlines
                
                let mut tokenizer = Tokenizer::new(Some(file), &contents, &token_arena, &string_table, &mut token_bucket_array);
                if let Err(e) = tokenize(&mut tokenizer) { anstream::println!("{}", e.msg); return; }
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

                let mut tokenizer = Tokenizer::new(None, &input, &token_arena, &string_table, &mut token_bucket_array);
                if let Err(e) = tokenize(&mut tokenizer) { anstream::println!("{}", e.msg); continue; }
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
