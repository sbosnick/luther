// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

extern crate luther;

#[macro_use]
extern crate luther_derive;

use luther::Lexer;
use luther::spanned::StrExt;

#[derive(Lexer, Debug, PartialEq)]
enum Token {
    #[luther(regex = "auto")] Auto,
    #[luther(regex = "break")] Break,
    #[luther(regex = "case")] Case,
    #[luther(regex = "char")] Char,
    #[luther(regex = "const")] Const,
    #[luther(regex = "continue")] Continue,
    #[luther(regex = "default")] DefaultKW,
    #[luther(regex = "do")] Do,
    #[luther(regex = "double")] Double,
    #[luther(regex = "else")] Else,
    #[luther(regex = "enum")] Enum,
    #[luther(regex = "extern")] Extern,
    #[luther(regex = "float")] Float,
    #[luther(regex = "for")] For,
    #[luther(regex = "goto")] Goto,
    #[luther(regex = "if")] If,
    #[luther(regex = "inline")] Inline,
    #[luther(regex = "int")] Int,
    #[luther(regex = "long")] Long,
    #[luther(regex = "register")] Register,
    #[luther(regex = "restrict")] Restrict,
    #[luther(regex = "return")] Return,
    #[luther(regex = "short")] Short,
    #[luther(regex = "signed")] Signed,
    #[luther(regex = "sizeof")] Sizeof,
    #[luther(regex = "static")] Static,
    #[luther(regex = "struct")] Struct,
    #[luther(regex = "switch")] Switch,
    #[luther(regex = "typeof")] Typedef,
    #[luther(regex = "union")] Union,
    #[luther(regex = "unsigned")] Unsigned,
    #[luther(regex = "void")] Void,
    #[luther(regex = "volitile")] Volatile,
    #[luther(regex = "while")] While,
    #[luther(regex = "_Alignas")] Alignas,
    #[luther(regex = "_Alignof")] Alignof,
    #[luther(regex = "_Atomic")] Atomic,
    #[luther(regex = "_Bool")] Bool,
    #[luther(regex = "_Complex")] Complex,
    #[luther(regex = "_Generic")] Generic,
    #[luther(regex = "_Imaginary")] Imaginary,
    #[luther(regex = "_Noreturn")] Noreturn,
    #[luther(regex = "_Static_assert")] StaticAssert,
    #[luther(regex = "_Thread_local")] ThreadLocal,
    #[luther(regex = "__func__")] FuncName,
    #[luther(regex = r"\.\.\.")] Ellipsis,
    #[luther(regex = r">>=")] RightAssign,
    #[luther(regex = r"<<=")] LeftAssign,
    #[luther(regex = r"\+=")] AddAssign,
    #[luther(regex = r"-=")] SubAssign,
    #[luther(regex = r"\*=")] MulAssign,
    #[luther(regex = r"/=")] DivAssign,
    #[luther(regex = r"%=")] ModAssign,
    #[luther(regex = r"\&=")] AndAssign,
    #[luther(regex = r"^=")] XorAssign,
    #[luther(regex = r"\|=")] OrAssign,
    #[luther(regex = r">>")] RightOp,
    #[luther(regex = r"<<")] LeftOp,
    #[luther(regex = r"\+\+")] IncOp,
    #[luther(regex = r"--")] DecOp,
    #[luther(regex = r"->")] PtrOp,
    #[luther(regex = r"\&\&")] AndOp,
    #[luther(regex = r"\|\|")] OrOp,
    #[luther(regex = r"<=")] LeOp,
    #[luther(regex = r">=")] GeOp,
    #[luther(regex = r"==")] EqOp,
    #[luther(regex = r"!=")] NeOp,
    #[luther(regex = r";")] Semicolon,
    #[luther(regex = r"{|<%")] LeftBrace,
    #[luther(regex = r"}|%>")] RightBrace,
    #[luther(regex = r",")] Comma,
    #[luther(regex = r":")] Colon,
    #[luther(regex = r"=")] Equals,
    #[luther(regex = r"\(")] LeftParen,
    #[luther(regex = r"\)")] RightParen,
    #[luther(regex = r"\[|<:")] LeftSquareBracket,
    #[luther(regex = r"\]|:>")] RightSquareBracket,
    #[luther(regex = r"\.")] Period,
    #[luther(regex = r"\&")] Ampersand,
    #[luther(regex = r"!")] Exclamation,
    #[luther(regex = r"\~")] Tilde,
    #[luther(regex = r"-")] Sub,
    #[luther(regex = r"\+")] Add,
    #[luther(regex = r"\*")] Mul,
    #[luther(regex = r"/")] Div,
    #[luther(regex = r"%")] Mod,
    #[luther(regex = r"<")] Less,
    #[luther(regex = r">")] Greater,
    #[luther(regex = r"^")] Caret,
    #[luther(regex = r"\|")] Bar,
    #[luther(regex = r"\?")] Question,
    #[luther(regex = r"[a-zA-Z_][a-zA-Z0-9_]*")] Identifier,
    #[luther(regex = r" +")] WhiteSpace,

    #[luther(regex = r"([1-9][0-9]*|0[0-7]*|0[xX][0-9a-fA-F]+)(([uU]([lL]|ll|LL)?)|(([lL]|ll|LL)[uU]?))?")]
    IConstant,

    #[luther(regex = r#"[uUL]?'([^'\\\n]|(\\(['"\?\\abfnrtv])|[0-7][[0-7]?[0-7]?|x[0-9a-fA-F]+))+'"#)]
    IConstantChar,

    #[luther(regex = r"(([0-9]+[eE][+-]?[0-9]+)|([0-9]*\.[0-9]+([eE][+-]?[0-9]+)?)|([0-9]+\.([eE][+-]?[0-9]+)?)|(0[xX][0-9a-fA-F]+[pP][+-]?[0-9]+)|(0[xX][0-9a-fA-F]*\.[0-9a-fA-F]+[pP][+-]?[0-9]+)|(0[xX][0-9a-fA-F]+\.[pP][+-]?[0-9]+))[fFlL]?")]
    FConstant,

    #[luther(regex = r#"((u8|[uUL])?"([^"\\\n]|\\(['"\?\\abfnrtv]|[0-7][0-7]?[0-7]?|x[0-9a-fA-F]*))*" *)+"#)]
    StringLiteral,
}

#[test]
fn token_lexes_keywords_punctuation_and_identifiers() {
    use Token::*;
    let input = "for foo >>".spanned_chars();

    let sut = Token::lexer(input).map_span(|s| s.into_inner().1);
    let results: Result<Vec<_>, _> = sut.collect();

    assert_eq!(
        results.expect("Unexpected error in the lexer."),
        vec![For, WhiteSpace, Identifier, WhiteSpace, RightOp]
    );
}
