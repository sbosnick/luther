# Luther

**Luther is an embedded lexer generator for stable Rust.**

[![Build Status](https://travis-ci.org/sbosnick/luther.svg?branch=master)](https://travis-ci.org/sbosnick/luther)
[![Coverage Status](https://coveralls.io/repos/github/sbosnick/luther/badge.svg?branch=master)](https://coveralls.io/github/sbosnick/luther?branch=master)
[![Latest Version](https://img.shields.io/crates/v/luther.svg)](https://crates.io/crates/luther)
[![Rust documentation](https://img.shields.io/badge/api-rustdoc-blue.svg)](https://docs.rs/luther/0.1.0/luther/)
---

Luther generates the lexer through its macros 1.1 derive implementation in the [luther-derive]
crate. You annotate your token `enum` with regular expressions (through the `#[luther(...)]`
attribute) and then `#[derive(Lexer)]` on it. Unlike many other approaches in Rust to lexing 
(or tokenizing), Luther does not operate on `&str` but rather on `char` iterators. The 
`luther::spanned` module, though, contains extension traits to produce such `char` iterators
from a `&str` or from a `std::io::Read` implementation.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependancies]
luther="0.2"
luther-dervice="0.2
```

and this to your crate root:

```rust
extern crate luther;
#[macro_use]
extern crate luther_derive;
```

## Example

```rust
extern crate luther;
#[macro_use]
extern crate luther_derive;

use luther::spanned::StrExt;

#[derive(Lexer)]
enum Token {
    #[luther(regex="ab")]
    Ab,

    #[luther(regex="acc*")]
    Acc,
}

fn main() {
    use luther::Lexer;

    let input = "abacaccabacccc".spanned_chars();   // from luther::spanned::StrExt

    let tokens = Tokens::lexer(input)
        .map_span(|s| s.into_inner());

    // use tokens
}
```

The `tokens` iterator from the above example will yield the following tokens
(together with their start and end locations):

- Token::Ab
- Token::Acc
- Token::Acc
- Token::Ab
- Token::Acc

The procedural macro implementation that provides the `#[derive(Lexer)]` and
recognized the `#[luther(...)]` attributes is in the [luther-derive] crate.

The intention is for the `tokens` iterator from the above example to be a
suitable candidate for an external lexer for the parser generator [Lalrpop].

[luther-derive]:https://crates.io/crates/luther-derive
[Lalrpop]:https://crates.io/crates/lalrpop

## License

Luther is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE-2.0](LICENSE-APACHE-2.0) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.

## Contribution

Please note that this project is released with a [Contributor Code of Conduct][code-of-conduct].
By participating in this project you agree to abide by its terms.

You may wish to review our [Contributing Guidelines][guidelines] before making a contribution.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in Luther by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[code-of-conduct]: CODE_OF_CONDUCT.md
[guidelines]: CONTRIBUTING.md
