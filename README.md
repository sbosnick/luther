# Luther

**Luther is an embedded lexer generator for stable Rust.**
[![Build Status](https://travis-ci.org/sbosnick/luther.svg?branch=master)](https://travis-ci.org/sbosnick/luther)
---
## Usage

Luther is current very much a work in progress. The following roughly how it works:

```rust
extern crate luther;
#[macro_use]
extern crate luther_derive;

#[derive(Lexer)]
enum Token {
    #[luther(regex="ab")]
    Ab,

    #[luther(regex="acc*")]
    Acc,
}

fn main() {
    use luther::Lexer;

    let input = ... // some suitable iterator

    let tokens = Tokens::lexer(input)
        .map(|r| r.map(|s| s.into_inner()));

    // use tokens
}
```

The syntax outlined above has a few rough edges that should be smothed out
before Luther is ready for prime-time.

The intention is for the `tokens` iterator from the above example to be a
suitable candate for an external lexer for the parser generator [Lalrpop].

[Lalrpop]:https://crates.io/crates/lalrpop

## License

Luther is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE-2.0](LICENSE-APACHE-2.0) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in Luther by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
