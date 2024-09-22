use bumpalo::Bump;
use src_proc_macros::InitKeywords;
use string_interner::backend::StringBackend;
use string_interner::StringInterner;

use crate::parse::token::Atom;

#[allow(non_snake_case)]
#[derive(InitKeywords, Clone)] 
pub struct Keywords {
    pub True: Atom,
    pub False: Atom,
    pub None: Atom,
    pub and: Atom,
    pub or: Atom,
    pub not: Atom,
    pub r#as: Atom,
    pub assert: Atom,
    pub r#async: Atom,
    pub r#await: Atom,
    pub class: Atom,
    pub r#struct: Atom,
    pub r#continue: Atom,
    pub def: Atom,
    pub del: Atom,
    pub elif: Atom,
    pub r#else: Atom,
    pub except: Atom,
    pub finally: Atom,
    pub r#for: Atom,
    pub from: Atom,
    pub global: Atom,
    pub r#if: Atom,
    pub import: Atom,
    pub r#in: Atom,
    pub is: Atom,
    pub lambda: Atom,
    pub nonlocal: Atom,
    pub pass: Atom,
    pub r#try: Atom,
    pub r#while: Atom,
    pub with: Atom,
    pub r#yield: Atom,
}

pub struct Context<'mem> {
    pub arena: &'mem Bump, 
    pub keywords: Keywords,
}

