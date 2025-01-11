#![feature(proc_macro_quote)]

use syn::{parse_macro_input, Data, DeriveInput};
use proc_macro::TokenStream;
use quote::quote;

#[proc_macro_derive(InitKeywords)]
pub fn derive_init_keywords(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let Data::Struct(struct_data) = input.data else { unimplemented!(); };

    let fields_as_idents: Vec<_> = struct_data.fields.iter().map(|field| {
        let Some(ident) = &field.ident else { unimplemented!(""); };
        quote! {#ident }
    }).collect();

    let fields_as_strings = struct_data.fields.iter().map(|field| {
        let Some(ident) = &field.ident else { unimplemented!(""); };
        ident.to_string()
    });

    let expanded = quote! {
        impl #name {
            pub fn new(string_arena: &mut string_interner::StringInterner<string_interner::backend::StringBackend>) -> Self {
                Self {
                    #( #fields_as_idents : Atom(string_arena.get_or_intern_static((#fields_as_strings).trim_start_matches("r#"))), )*
                }
            }

            pub fn is_keyword(&self, atom: Atom) -> bool {
                #( if self.#fields_as_idents == atom { return true; } )*
                false
            }
        }
    };

    TokenStream::from(expanded)

    // "fn answer() -> u32 { 42 }".parse().unwrap()
}