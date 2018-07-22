# A Coq frontend to check answers of SAT-Solvers.

## TCB (ie [Trusted Computing Base](https://en.wikipedia.org/wiki/Trusted_computing_base))

The TCB in our proof includes the Coq proof assistant, the OCaml compiler, and our process to link our OCaml oracles to our Coq code through Coq extraction. In particular, we conjecture that it is sound to declare imperative polymorphic oracles in Coq, by encapsulating their results in our [Impure Monad](Impure/ImpMonads.v). In other words, we conjecture that the partial correctness properties that we have proved in Coq on functions invoking are preserved by Coq extraction and OCaml compilation. For instance, see axiom `next` of [RatProver](RatProver.v).

Moreover, the inputs/outputs of `satans-cert` are currently unchecked, as detailed just below. Hence, input/output functions of our `satans-cert` are also in the TCB.

## The (partial) correctness properties that we formally prove

The main code of `satans-cert` is defined in [SatAnsCert](SatAnsCert.v) together with the proof of partial correctness.
In this code, we (only) prove properties on the CNF produced by oracle `read_input` from the parsing of the DIMACS file given on the command line.
This CNF is thus expected to be an abstract syntax of the one specified by the DIMACS file. Formally, this notion of CNF is defined in [CnfSpec](CnfSpec.v).

We prove that

  - if "SAT !" is finally printed then the CNF returned by `read_input` is sat.

  - if "UNSAT !" is finally printed then the CNF returned by `read_input` is unsat.

Technically, the two above properties are ensured by an `ASSERT` in each branch leading to the corresponding `println` command.

## Overview of the certified code

TODO
