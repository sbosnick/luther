// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

extern crate luther_redfa;

// This test currently reveals the patholocial memory use in luther_redfa.
// Running it takes waaaay too long so ignore it for now until the patholocial
// memory use has been corrected.
#[test]
#[ignore]
fn clang_token_dfa_has_reasonable_number_of_tokens() {
    let tokens = vec![
        "auto",
        "break",
        "case",
        "char",
        "const",
        "continue",
        "default",
        "do",
        "double",
        "else",
        "enum",
        "extern",
        "float",
        "for",
        "goto",
        "if",
        "inline",
        "int",
        "long",
        "register",
        "restrict",
        "return",
        "short",
        "signed",
        "sizeof",
        "static",
        "struct",
        "switch",
        "typeof",
        "union",
        "unsigned",
        "void",
        "volitile",
        "while",
        "_Alignas",
        "_Alignof",
        "_Atomic",
        "_Bool",
        "_Complex",
        "_Generic",
        "_Imaginary",
        "_Noreturn",
        "_Static_assert",
        "_Thread_local",
        "__func__",
        r"\.\.\.",
        r">>=",
        r"<<=",
        r"\+=",
        r"-=",
        r"\*=",
        r"/=",
        r"%=",
        r"\&=",
        r"\^=",
        r"\|=",
        r">>",
        r"<<",
        r"\+\+",
        r"--",
        r"->",
        r"\&\&",
        r"\|\|",
        r"<=",
        r">=",
        r"==",
        r"!=",
        r";",
        r"\{|<%",
        r"}|%>",
        r",",
        r":",
        r"=",
        r"\(",
        r"\)",
        r"\[|<:",
        r"\]|:>",
        r"\.",
        r"\&",
        r"!",
        r"\~",
        r"-",
        r"\+",
        r"\*",
        r"/",
        r"%",
        r"<",
        r">",
        r"\^",
        r"\|",
        r"\?",
        r"[a-zA-Z_][a-zA-Z0-9_]*",
        r" +",
        r"([1-9][0-9]*|0[0-7]*|0[xX][0-9a-fA-F]+)(([uU]([lL]|ll|LL)?)|(([lL]|ll|LL)[uU]?))?",
        r#"[uUL]?'([^'\\\n]|(\\(['"\?\\abfnrtv])|[0-7][0-7]?[0-7]?|x[0-9a-fA-F]+))+'"#,
        r"(([0-9]+[eE][+-]?[0-9]+)|([0-9]*\.[0-9]+([eE][+-]?[0-9]+)?)|([0-9]+\.([eE][+-]?[0-9]+)?)|(0[xX][0-9a-fA-F]+[pP][+-]?[0-9]+)|(0[xX][0-9a-fA-F]*\.[0-9a-fA-F]+[pP][+-]?[0-9]+)|(0[xX][0-9a-fA-F]+\.[pP][+-]?[0-9]+))[fFlL]?",
        r#"((u8|[uUL])?"([^"\\\n]|\\(['"\?\\abfnrtv]|[0-7][0-7]?[0-7]?|x[0-9a-fA-F]*))*" *)+"#,
    ];

    let ctx = luther_redfa::Context::new();
    let dfa = ctx.from_regex_vec(tokens)
        .expect("Error parsing c language token regular expressions.");
    let count = dfa.states().count();

    // the 100 to 130 range has a midpoint of 115 which is what Owens et al.
    // reported as the number of states their implemention came up with for the
    // CKit lexer for ANSI C.
    assert!(100 <= count && count <= 130);
}
