#![feature(allocator_api)]

use anstyle::{AnsiColor, Reset, RgbColor};
use bumpalo::Bump;
use clap::Parser;

use itertools::enumerate;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use string_interner::StringInterner;

use core::str;
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

const DEBUG_TOKENS: bool = false;

fn tokenize<'source, 'c, 'd>(tokenizer: &mut Tokenizer<'source, 'c, 'd>) -> Result<usize, SyntaxError> {
    let mut tokens = Vec::<Token>::new();

    let mut token_count = 0usize;
    while let Some(token) = tokenizer.next_token()? {
        if DEBUG_TOKENS {
            println!("{}:    {:?}", tokens.len() + 1, token);
            match token.value {
                TokenValue::Identifier(atom) => println!("Ident: {}", tokenizer.context.string_arena.resolve(atom).unwrap_or_default()),
                _ => {}
            }
            tokens.push(token);
        }
        token_count += 1;
    }
    
    println!("Count: {}", token_count);

    if DEBUG_TOKENS {
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
    }
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

    let mut string_arena = StringInterner::default();

    let parser_arena = Bump::new();
    
    let keywords = Keywords::new(&mut string_arena);
    let mut parser_context = ParserContext {
        arena: &parser_arena,
        string_arena: &mut string_arena,
        keywords
    };

    if !args.add.is_empty() {
        let mut tokenizer = Tokenizer::new(Some("<--add>".to_string()), &args.add, &mut parser_context);
        if let Err(e) = tokenize(&mut tokenizer) { anstream::println!("{}", e.msg); return; }
    }
    
    if !args.run.is_empty() {
        let mut tokenizer = Tokenizer::new(Some("<--run>".to_string()), &args.run, &mut parser_context);
        if let Err(e) = tokenize(&mut tokenizer) { anstream::println!("{}", e.msg); return; }
        return;
    }

    if let Some(file) = args.file {
        match fs::read_to_string(&file) {
            Ok(mut contents) => {
                contents = contents.trim_start_matches("\u{feff}").to_string().replace("\r\n", "\n"); // Handle BOM and Windows newlines
                
                let mut tokenizer = Tokenizer::new(Some(file), &contents, &mut parser_context);
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

                let mut tokenizer = Tokenizer::new(None, &input, &mut parser_context);
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
