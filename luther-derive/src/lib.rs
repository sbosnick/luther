// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

extern crate proc_macro;
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use syn::DeriveInput;

#[proc_macro_derive(Lexer, attributes(luther))]
pub fn luther_derive(input: TokenStream) -> TokenStream {
    let _ast: DeriveInput = syn::parse(input).expect("failed to parse the input token stream");

    let expanded = quote!{};

    expanded.into()
}
