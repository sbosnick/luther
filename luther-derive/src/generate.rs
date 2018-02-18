// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use syn::{self, Ident};
use quote;
use redfa;
use enum_info;

type State<'ast> = redfa::State<char, Option<enum_info::VariantInfo<'ast>>>;
type Dfa<'ast> = redfa::Dfa<char, Option<enum_info::VariantInfo<'ast>>>;

pub fn generate_lexer_impl<'ast>(
    info: &'ast enum_info::EnumInfo<'ast>,
    dfa: &'ast Dfa<'ast>,
    error_state: usize,
) -> quote::Tokens {
    let name = info.name;
    let dfa_name = Ident::from(&info.dfa_name as &str);
    let dfa_enum = generate_dfa_enum(dfa_name, dfa.states.len());
    let dfa_default = generate_dfa_default(dfa_name);
    let is_error_fn = generate_is_error_fn(dfa_name, error_state);
    let transition_fn = generate_transition_fn(dfa, dfa_name, error_state);
    let accept_fn = generate_accept_fn(dfa, dfa_name, *name);

    quote!{
        #dfa_enum

        #dfa_default

        impl luther::dfa::Dfa<#name> for #dfa_name {
            #is_error_fn

            #transition_fn

            #accept_fn
        }

        impl ::luther::Lexer for #name {
            type Dfa = #dfa_name ;
        }
    }
}

fn generate_dfa_enum(dfa_name: Ident, num_states: usize) -> quote::Tokens {
    let state_name = (0..num_states).map(make_state_name);

    quote! {
        #[derive(PartialEq, Debug, Clone, Copy)]
        enum #dfa_name {
            #(#state_name),*
        }
    }
}

fn generate_dfa_default(dfa_name: Ident) -> quote::Tokens {
    let state_path = make_state_path(dfa_name, 0);

    quote! {
        impl Default for #dfa_name {
            fn default() -> Self {
                #state_path
            }
        }
    }
}

fn generate_is_error_fn(dfa_name: Ident, error_state: usize) -> quote::Tokens {
    let state_path = make_state_path(dfa_name, error_state);

    quote! {
        fn is_error(&self) -> bool {
            *self == #state_path
        }
    }
}

fn generate_transition_fn(dfa: &Dfa, dfa_name: Ident, error_state: usize) -> quote::Tokens {
    let error_state_name = make_state_path(dfa_name, error_state);
    let state_transitions = dfa.states.iter().enumerate().map(|(state_num, state)| {
        generate_trasitions_for_state(state, dfa_name, state_num, error_state)
    });

    quote! {
        fn transition(&self, c: char) -> Self {
            match (*self, c) {
                #(#state_transitions)*
                (_, _) => #error_state_name,
            }
        }
    }
}

fn generate_trasitions_for_state(
    state: &State,
    dfa_name: Ident,
    state_num: usize,
    error_state: usize,
) -> quote::Tokens {
    let state_path = make_state_path(dfa_name, state_num);
    let default = state.default as usize;

    let default_transition = if default == error_state {
        quote!{}
    } else {
        let default_state = make_state_path(dfa_name, default);
        quote!{ (#state_path, _) => #default_state, }
    };

    let from = (0..state.by_char.len()).map(|_| make_state_path(dfa_name, state_num));
    let label = state.by_char.keys();
    let to = state
        .by_char
        .values()
        .map(|&i| make_state_path(dfa_name, i as usize));

    quote! {
        #((#from, #label) => #to),*
        #default_transition
    }
}

fn generate_accept_fn(dfa: &Dfa, dfa_name: Ident, name: Ident) -> quote::Tokens {
    let state_accepts = dfa.states
        .iter()
        .enumerate()
        .map(|(state_num, state)| generate_accept_for_state(state, dfa_name, state_num, name));

    quote!{
        fn accept(&self, _matched: &str) -> Option<#name> {

            match *self {
                #(#state_accepts)*
                _ => None,
            }
        }
    }
}

fn generate_accept_for_state(
    state: &State,
    dfa_name: Ident,
    state_num: usize,
    name: Ident,
) -> quote::Tokens {
    state.value.as_ref().map_or(quote!{}, |variant| {
        let state_name = make_state_path(dfa_name, state_num);
        let token_name = variant.name;
        let field_builder = variant
            .field
            .map_or(quote!{}, |_| quote!{(_matched.parse().unwrap_or_default())});
        quote!{#state_name => Some(#name::#token_name#field_builder),
        }
    })
}

fn make_state_name(state_num: usize) -> Ident {
    format!("State{}", state_num).into()
}

fn make_state_path(dfa_ident: Ident, state_num: usize) -> syn::Path {
    syn::Path {
        leading_colon: None,
        segments: vec![dfa_ident, make_state_name(state_num)]
            .into_iter()
            .map(|s| syn::PathSegment::from(s))
            .collect(),
    }
}
