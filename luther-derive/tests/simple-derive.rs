extern crate luther;

#[macro_use]
extern crate luther_derive;

#[macro_use]
extern crate failure;

#[macro_use]
extern crate assert_matches;

#[derive(Lexer, Debug)]
enum Token {
    #[luther(regex = "ab")] Ab,
    #[luther(regex = "acc*")] Acc,
    #[luther(regex = "a(bc|de)")] Abcde(String),
}

#[derive(Fail, Debug)]
enum NoError {}

impl std::fmt::Display for NoError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "The impossible has occured.")
    }
}

struct SpanedStrIter<I>
where
    I: Iterator<Item = (usize, char)>,
{
    inner: I,
}

impl<'a> SpanedStrIter<std::str::CharIndices<'a>> {
    fn new(input: &'a str) -> Self {
        SpanedStrIter {
            inner: input.char_indices(),
        }
    }
}

impl<I> Iterator for SpanedStrIter<I>
where
    I: Iterator<Item = (usize, char)>,
{
    type Item = Result<luther::Span<char>, NoError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(i) => Some(Ok(i.into())),
        }
    }
}

#[test]
fn token_lexes_ab() {
    use luther::Lexer;
    let input = SpanedStrIter::new("ab");

    let mut sut = Token::lexer(input).map(|r| r.map(|s| s.into_inner().1));
    let result = sut.next();

    assert_matches!(result, Some(Ok(Token::Ab)));
}

#[test]
fn token_lexes_ade() {
    use luther::Lexer;
    let input = SpanedStrIter::new("ade");

    let mut sut = Token::lexer(input).map(|r| r.map(|s| s.into_inner().1));
    let result = sut.next();

    assert_matches!(result, Some(Ok(Token::Abcde(ref s))) if s == "ade");
}
