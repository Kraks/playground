Artifact for Compiling to Summaries
===

Author: Guannan Wei <guannanwei@purdue.edu>

This is the accompanying artifact for CS592 project (Compiling to Summaries).

The main content of the artifact is a ``partial'' abstract interpreter.
Given an incomplete program (e.g. just a function), the ``partial'' abstract
interpreter can (1) perform possible analysis within this incomplete program,
and (2) generate code that performs analysis depending on other currently
unknown programs.

## Requirement

To run the project, the minimal requirement is to have JDK (version >= 8) installed.

## How to Run

The artifact is a Scala 3 project, managed by `sbt`.

Run `sbt compile` to compile the project and run `sbt test` to check some basic functionalities.

## Files

Source code files of the implementation are stored under `src/main/scala/`.

- `WhileFun.scala`: the language definition, which is a first-order functional language
with arithmetic, conditional, loop, nested control flow structure, and return statement.
- `Examples.scala`: some example programs (AST) written in this language.
- `Concrete.scala`: a standard concrete semantics.
- `Domain.scala`: definitions for lattice, abstract domain, and numerical domain.
The file also contains instances of lattices for built-in structures (e.g. product and map).
- `Interval.scala`: the definition of interval abstract domain.
- `Abstract.scala`: an abstract interpreter using the interval domain.
- `PartialAbstract.scala`:
- `RetVal.scala`: an abstract domain to model return behavior with higher precision (currently not used)

