#![feature(allocator_api)]

#![feature(f16)]
#![feature(f128)]

use anstyle::{AnsiColor, Reset, RgbColor};

use clap::Parser;

use display_tree::println_tree;
use itertools::enumerate;
use lazy_static::lazy_static;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use core::str;
use std::{fs::File, io::Read, sync::RwLock};

mod annotations;

mod parse;
use parse::*;

mod utf8;
use utf8::*;

#[derive(clap::Parser, Debug)]
#[command(version = "0.0.1", about = "Interpreter and compiler for a language.", long_about = None)]
struct Args {
    #[arg(help = "The file to start running from.")]
    file: Option<String>,

    #[arg(short, long, default_value = "", help = "Parse and interpret a string before the beginning of the program.")]
    add: String,

    #[arg(short, long, conflicts_with = "file", default_value = "", help = "Runs the provided string as a standalone program.")]
    run: String,

    #[arg(short, long, help = "Prints the inputs passed to the tokenizer as colored segmented tokens.")]
    debug_tokens: bool,
}

lazy_static! {
    static ref DEBUG_TOKENS: RwLock<bool> = RwLock::new(false);
}

fn tokenize(filename: Option<String>, source: &'static str) -> Result<TokensVec, SyntaxErrRef> {
    let tokenizer = Tokenizer::new(filename, source);
    let tokens = tokenizer.collect()?;

    println!("Token Count: {}", tokens.len());

    if *DEBUG_TOKENS.read().unwrap() {
        for (i, t) in enumerate( &tokens) {
            println!("{}:    {:?}", i + 1, t);
            if let TokenValue::Identifier(atom) = t.value { println!("Ident: {}", STRING_ARENA.lock().unwrap().resolve(atom.0).unwrap()) }
        }

        let colors = [RgbColor(237, 174, 73), RgbColor(209, 73, 91), RgbColor(0, 121, 140), RgbColor(202, 255, 208)];

        let mut color = 0;
        for t in &tokens {
            color = (color + 1) % colors.len();

            let c = colors[color];

            anstream::print!("{}", &source[t.range_of_leading_white_space()]);
            
            let s = &source[t.loc.range.clone()];
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

            anstream::print!("{}", &source[t.range_of_trailing_white_space()]);
        }
        anstream::println!("{}", Reset.render());
    }
    Ok(tokens)
}


fn parse(filename: Option<String>, source: &'static str) -> Result<AstRef, SyntaxErrRef> {
    let mut parser = crate::parse::Parser::new(filename, source)?;
    let ast = parser.parse()?;
    println_tree!(ast);
    Ok(ast)
}

fn main() {
    let args = Args::parse();
    *DEBUG_TOKENS.write().unwrap() = args.debug_tokens;

    std::env::set_var("RUST_BACKTRACE", "verbose");

    let parser_arena: ArenaRef = PARSER_ARENA.get_or(|| PARSER_ARENA_HERD.get());

    if !args.add.is_empty() {
        let source = parser_arena.alloc_str(&args.add);
        if let Err(e) = parse(Some("<--add>".to_string()), source) { anstream::println!("{}", e); return; }
    }
    
    if !args.run.is_empty() {
        let source = parser_arena.alloc_str(&args.run);
        if let Err(e) = parse(Some("<--run>".to_string()), source) { anstream::println!("{}", e); return; }
        return;
    }

    if let Some(filepath) = args.file {
        match File::open(filepath.clone()) {
            Ok(mut file) => {
                let size = file.metadata().map(|m| m.len() as usize).ok().unwrap_or(0);

                let mut buffer = vec![0; size];
                let mut buffer = buffer.as_mut_slice();
                
                file.read_exact(buffer).expect("internal error; file read was different size than allocated");
                buffer = utf8_normalize_newlines_and_remove_bom(buffer);

                let mut contents: Vec<u8> = Vec::with_capacity(size);

                let mut repl = [0; 4];
                char::REPLACEMENT_CHARACTER.encode_utf8(repl.as_mut_slice());

                for chunk in Utf8Lossy::from_bytes(buffer).chunks() {
                    contents.extend_from_slice(chunk.valid.as_bytes());
                    if !chunk.broken.is_empty() {
                        contents.extend_from_slice(repl.as_slice());
                    }
                }

                let contents_str = parser_arena.alloc_str(unsafe { str::from_utf8_unchecked(contents.as_slice()) });
                if let Err(e) = parse(Some(filepath), contents_str) { anstream::println!("{}", e); return; }

            }
            Err(err) => println!("{}: {}", &filepath, err),
        }
        return;
    } 

    println!("Language interpreter");
    println!("Type \"exit()\", Ctrl+C or Ctrl+D to exit.");

    let mut input = String::with_capacity(50);

    let mut rl = DefaultEditor::new().unwrap();
    loop {
        match rl.readline(if input.is_empty() { ">>> " } else { "... " }) {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str());
                input.push_str(line.as_str());
                input = input.replace("\r\n", "\n"); // Handle Windows newlines

                if input.trim_end() == "exit()" { break; } 
                
                if input.ends_with("\\") { 
                    // Line continuations
                    input.push('\n');
                    continue;
                }

                // We need to keep all sources alive statically, since
                // input is overwritten on the next interactive input.
                // Tokens and the Ast need to refer to the source they were parsed from.
                let source = parser_arena.alloc_str(&input);
                if let Err(e) = parse(None, source) { 
                    if e.in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines {
                        input.push('\n');

                        continue; // To read another line and try again
                    } else {
                        anstream::println!("{}", e); 
                        
                        input.clear();
                        continue; 
                    }
                } else {
                    input.clear();
                    // TODO: Do stuff with AST!
                }
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
