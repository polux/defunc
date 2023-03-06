# Functional Toolbox

*Disclaimer: this is not an official Google product*

A set of program-to-program transformations and a commandline tool for applying
them. The goal is to automate as much as possible the transformations studied by
Danvy et al. which relate various forms of abstract machines and interpreters.
The paper [Defunctionalized Interpreters for Programming Languages][1] offers a
good overview of these transformations.

Currently implemented transformations are:

  - One-pass CPS
  - Defunctionalization

The object language is a call-by-value untyped lambda-caculus augmented with
constructors and pattern matching. Interesting examples can be found under
`examples`.

Example usage:

```
cabal run defunc -- parse eval < examples/append.lam
cabal run defunc -- parse cps < examples/append.lam
cabal run defunc -- parse cps defunc < examples/append.lam
cabal run defunc -- parse cps defunc eval < examples/append.lam
```

[1]: http://jfla.inria.fr/2014/danvy-ICFP08.pdf

