#![feature(allocator_api)]

use anstyle::{AnsiColor, Reset, RgbColor};
use bumpalo::BumpSync;
use bumpalo::Herd;

use clap::Parser;

use display_tree::println_tree;
use itertools::enumerate;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use string_interner::backend::StringBackend;
use string_interner::StringInterner;
use thread_local::ThreadLocal;

use core::str;
use std::fs;
use std::sync::Mutex;

mod annotations;

mod parse;
use parse::*;

mod bucket_array;

#[derive(clap::Parser, Debug)]
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

fn tokenize<'source>(filename: Option<String>, source: &'source str) -> Result<usize, SyntaxErr<'source>> {
    let tokenizer = Tokenizer::new(filename, source);
    let tokens = tokenizer.collect()?;

    if DEBUG_TOKENS {
        for t in &tokens {
            println!("{}:    {:?}", tokens.len() + 1, t);
            match t.value {
                TokenValue::Identifier(atom) => println!("Ident: {}", STRING_ARENA.lock().unwrap().resolve(atom).unwrap()),
                _ => {}
            }
        }
    }
    println!("Count: {}", tokens.len());

    if DEBUG_TOKENS {
        let colors = vec![RgbColor(237, 174, 73), RgbColor(209, 73, 91), RgbColor(0, 121, 140), RgbColor(202, 255, 208)];

        let mut color = 0;
        for t in &tokens {
            color = (color + 1) % colors.len();

            let c = colors[color];

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
        }
        anstream::println!("{}", Reset.render());
    }
    Ok(tokens.len())
}


fn parse<'source, 'mem>(filename: Option<String>, source: &'source str) -> Result<Option<AstRef>, SyntaxErr<'source>> {
    let mut parser = crate::parse::Parser::new(filename, source)?;
    let ast = parser.parse()?;

    if let Some(tree) = &ast {
        println_tree!(*tree);
    }

    Ok(ast)
}
use lazy_static::lazy_static;

pub type ArenaRef = &'static BumpSync<'static>;

lazy_static! {
    static ref STRING_ARENA: Mutex<StringInterner<StringBackend>> = Mutex::new(StringInterner::default());
    static ref KEYWORDS: Keywords = Keywords::new(&mut STRING_ARENA.lock().unwrap());

    static ref PARSER_ARENA_HERD: Herd = Herd::new();
    static ref PARSER_ARENA: ThreadLocal<BumpSync<'static>> = ThreadLocal::new();

    static ref AST_ARENA_HERD: Herd = Herd::new();
    static ref AST_ARENA: ThreadLocal<BumpSync<'static>> = ThreadLocal::new();
}

fn main() {
    let args = Args::parse();

    std::env::set_var("RUST_BACKTRACE", "full");

    if !args.add.is_empty() {
        if let Err(e) = parse(Some("<--add>".to_string()), &args.add) { anstream::println!("{}", e); return; }
    }
    
    if !args.run.is_empty() {
        if let Err(e) = parse(Some("<--run>".to_string()), &args.run) { anstream::println!("{}", e); return; }
        return;
    }

    if let Some(file) = args.file {
        match fs::read_to_string(&file) {
            Ok(mut contents) => {
                contents = contents.trim_start_matches("\u{feff}").to_string().replace("\r\n", "\n"); // Handle BOM and Windows newlines
                if let Err(e) = parse(Some(file), &contents) { anstream::println!("{}", e); return; }
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

                if let Err(e) = parse(None, &input) { 
                    if e.in_interactive_interpreter_should_discard_and_instead_read_more_lines {
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
