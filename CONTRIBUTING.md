# Contributing to Luther

First off, thank you for considering contributing to Luther. It is through contributions from
a wide range of people that we all can make open source software better.

Please reach out through a GitHub issue if we can do anything to help you contribute.

## Submitting bug reports and feature requests

When reporting a bug or asking for help, please include enough details so that
the people helping you can reproduce the behavior you are seeing. For some tips
on how to approach this, read about how to produce a [Minimal, Complete, and
Verifiable example].

[Minimal, Complete, and Verifiable example]: https://stackoverflow.com/help/mcve

When making a feature request, please make it clear what problem you intend to
solve with the feature, any ideas for how Luther could support solving that
problem, any possible alternatives, and any disadvantages.

## Building and testing

The Luther project is spread over several different crates, but they are all (currently)
part of the sbosnick/luther GitHub repository, and are all part of a cargo workspace rooted
at the root of the repository. To build all of the crates at once add the `--all` flag to
`cargo build` and `cargo test`.

There are two different parts to the test process. We encourage you to run both parts locally
before submitting a pull request as it will typically be easier to iterate and fix 
problems locally rather than wait for the CI servers to run the tests for you.

### In the root of the project

```sh
# Run all the unit, integration, and doc test.
cargo test --all
```

### In any directory in the project

```sh
# Run the luther-dervie test suite
cargo testsuite
```

The `luther-derive` test suite is in the `luther-derive/testsuite` subdirectory.
See the `README` file in that directory for more information about the test suite.

## Pull Requests

We encourage contributions through pull request. If you are thinking about 
implementing a medium or large new feature, though, you may want to discuss it through
a GitHub issue first. Generally all pull requests that add or change code (as 
opposed to just documentation change) should include new tests. Pull requests that 
introduce new features would (ideally) also include new documentation, though it 
doesn't have to be as extensive as it may eventually end up being.

## Test Coverage

We try to maintain a high degree of test coverage as reported by `coveralls.io`. 
The goal is to have `coveralls.io` report 100% coverage while minimizing the use
of the coverage exclusion flags: COV_EXCL_LINE, and the COV_EXCL_START and 
COV_EXCL_END pair. We try to keep any new uses of the coverage exclusion flags
in the source code of the project to their own separate commit so that the commit
message can give an explanation/justification for the exclusion.

If your contribution results in the test coverage going down from 100%, though,
you don't have too worry too much about it so long as your contribution contains
some tests. We can review the coverage reports at a later time to look for ways to
meaningfully increase the test coverage or to make judgment calls about excluding
some sections of the source code from test coverage.

## Code of Conduct

We follow a [Contributor Code of Conduct][code-of-conduct] in the Luther project.
By participating in this project you agree to abide by its terms.

[code-of-conduct]: CODE_OF_CONDUCT.md

One way that the Contributor Code of Conduct is currently deficient is the
lack of a means of reporting abusive, harassing, or otherwise unacceptable
behavior by the project leader (Steven Bosnick). While I (Steven Bosnick) 
intend for there to never be any reason for such a report, the project would
be improved greatly if there were a means to make such reports.

If someone who has had experience dealing with a Contributor Code of Conduct was
willing to act as the person to whom such reports could be directed then that
would be a very welcome contribution to the project. Please email the project
leader directly at "sbosnick at sympatico dot ca" if you are interested
in contributing in this manner.
