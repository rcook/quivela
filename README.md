[![Build Status](https://travis-ci.org/awslabs/quivela.svg?branch=master)](https://travis-ci.org/awslabs/quivela)

# quivela2 protocol verifier

`quivela2` is a tool to verify protocols modeled as object-oriented programs.

## Installation

`Quivela2` is written in Haskell and requires the
(stack)[https://docs.haskellstack.org/en/stable/README/] tool to be installed.
To build Quivela, run `stack build` in the source directory. To get a GHCi REPL
with the quivela modules loaded, run `stack ghci`.

To run, `quivela2` requires (z3)[https://github.com/Z3Prover/z3] to be installed
and executable (i.e. the binary should be in a directory listed in `$PATH` on
Linux/Mac systems).

## Usage

**Note that this document is a [Literate Haskell][literate-haskell] source file that you can compile and run as follows:**

```bash
stack test quivela:readme
```

Quivela2 proofs are developed in a Haskell source file that imports various Quivela2 modules and compiles against the `quivela` library. Proof sources will typically require both the `QuasiQuotes` and `TemplateHaskell` language extensions to be enabled and the `Quivela` and `Quivela.Language` modules to be imported. The `System.Exit` module can also be imported for later use in the `main` function:

```haskell
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Quivela
import Quivela.Language
import System.Exit
```

To prove programs equivalent, we construct a series of proof steps as a
Haskell expression and then invoke the verifier on it; here is a small example that shows that the `&` operator commutes (aside from the value it returns) and that `1 & x` is equivalent to `x`:

```haskell
andExample :: [ProofPart]
andExample =
  [prog| new() { method f(x, y) { 1 & x & y & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { 1 & y & x & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { y & x & 1 } } |]
  : []
```

Quivela2 programs are embedded into Haskell using the `prog` quasiquotation, which expands into parsing the given Quivela2 expression. The `≈` operator chains together several expressions. Since proofs are represented as lists, each proof must be terminated by `: []`.

To check this proof, load the file in `GHCi` and evaluate the following expression:

```.haskell .ignore
prove' emptyVerifyEnv nop andExample
```

The `prove'` function takes an environment as the first argument (usually `emptyVerifyEnv` if starting from scratch), an expression containing shared method definitions and global variable declarations as the second argument and a list of `ProofPart`s as the third argument.

To avoid having to manually evaluate a call to `prove'` after each modification, Quivela2 also provides a compile-time version called `prove` that will perform the verification as part of loading the file in GHCi. The proof above can then be written as follows:

```haskell
prove emptyVerifyEnv nop $
  [prog| new() { method f(x, y) { 1 & x & y & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { 1 & y & x & 1 } } |]
  ≈
  [prog| new() { method f(x, y) { y & x & 1 } } |]
  : []
```

Some steps may require additional proof hints. For example, to prove objects with mutable fields equivalent, it is often necessary to state an appropriate invariant:

```haskell
eqInvExample :: [ProofPart]
eqInvExample =
  [prog| new (x=0) { method f() { <x, x> } } |]
  ≈ Hint [ fieldsEqual ["x"] ["y"] ]:
  [prog| new (y=0) { method f() { <y, y> } } |]
  : []
```

Instead of stating many equality invariants on variables that are never modified, object fields can be declared as constant:

```haskell
prove emptyVerifyEnv nop $
  [prog| new (const x=0) { method f() { x } } |]
  ≈
  [prog| new (const x=0) { method f() { 0 } } |]
  : []
```

Multiple proofs can be run from the `main` function:

```haskell
main :: IO ()
main = do
  andResult <- prove' emptyVerifyEnv nop andExample
  eqInvResult <- prove' emptyVerifyEnv nop eqInvExample
  if andResult /= 0 || eqInvResult /= 0
    then exitFailure
    else exitSuccess
```

For a larger proof, please refer to [`ETM.hs`](src/ETM.hs).

## Open issues

There are number of side conditions that are currently not checked:

- Programs are not checked for termination

- Adversaries should also get access to the method name that was called on
  an adversary object.

- Previous proof steps are cached upon successful verification, but currently
  the cache does not include invariants were used to verify something. As a
  result, when changing invariants but not the programs in a proof step, the
  step will not be rechecked. This does not affect soundness, since the two
  programs are equivalent and the invariants are only used during this
  verification step.

- The concrete syntax is somewhat ugly in that semicolons are required as
  separators in between expressions, and methods need to be prefixed by the
  keyword "method".

- Rewriting with an assumption currently doesn't take bound variables into
  account. Also, assumptions are now implicit in the rewrite steps that
  are performed instead of stated upfront.

## Style guide

- Either import by name or qualify all imported identifiers.
- Run hindent (we use all default settings) before creating pull request.

[literate-haskell]: https://wiki.haskell.org/Literate_programming
