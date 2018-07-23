# A Coq frontend to check answers of SAT-Solvers.

## TCB (ie [Trusted Computing Base](https://en.wikipedia.org/wiki/Trusted_computing_base))

The TCB in our proof includes the Coq proof assistant, the OCaml compiler, and our process to link our OCaml oracles to our Coq code through Coq extraction. In particular, we conjecture that it is sound to declare imperative polymorphic oracles in Coq, by encapsulating their results in our [Impure](Impure/) monad. In other words, we conjecture that the partial correctness properties that we have proved in Coq on functions invoking are preserved by Coq extraction and OCaml compilation. For instance, see axiom `next` of [RatProver](RatProver.v).

Moreover, the inputs/outputs of `satans-cert` are currently unchecked, as detailed just below. Hence, input/output functions of our `satans-cert` are also in the TCB.

## The (partial) correctness properties that we formally prove

The main code of `satans-cert` is defined in [SatAnsCert](SatAnsCert.v) together with the proof of partial correctness.
In this code, we (only) prove properties on the CNF produced by oracle `read_input` from the parsing of the DIMACS file given on the command line.
This CNF is thus expected to be an abstract syntax of the one specified by the DIMACS file. Formally, this abstract syntax and its semantics are defined in [CnfSpec](CnfSpec.v).

We prove that

  - if "SAT !" is finally printed then the CNF returned by `read_input` is sat.

  - if "UNSAT !" is finally printed then the CNF returned by `read_input` is unsat.

Formally, the two above properties are ensured by an `ASSERT` in each branch leading to the corresponding `println` command.

## Overview of the implementation

As expected, the challenging part in the development of `satans-cert` is to efficiently verify UNSAT answers. On such an answer, our certified [RatProver](RatProver.v) invokes an external untrusted LRAT parser (through the `next` axiom mentioned above). Here, the main contribution of our development -- w.r.t others like [coq-lrat](https://github.com/arpj-rebola/coq-lrat) -- comes from the design of this `RatProver`. Indeed, the external parser extends internally the current CNF with RUP clauses (ie auxiliary lemmas learned by CDCL SAT-solvers) through a Coq-certified `rup_learn` function. A [parametric proof](http://homepages.inf.ed.ac.uk/wadler/topics/parametricity.html) expresses that the parser can only build new clauses that are logical consequences of the CNF, through this `rup_learn` function. This style is called "polymorphic LCF style" (in reference to the [LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions) prover at the origin of [ML](https://en.wikipedia.org/wiki/ML_(programming_language)).

A benefit of this design is to keep the dictionary of learned clauses inside the external parser (this dictionary is thus implemented as a polymorphic hash-table). In short, this design makes our prover both simple to certify and efficient on RUP clause checking.

- [CnfSpec](CnfSpec.v) defines the abstract syntax of CNF and its semantics.

- [SatProver](SatProver.v) defines the certified checker that a CNF is Sat (with a more concrete representation of CNF models than in `CnfSpec`).

- [SolverInterface](SolverInterface.v) defines the data-types exchanged with the external Solver.

- [Rup](Rup.v) defines and proves the verification of Backward Resolution Chains: such a chain is a proof that RUP clauses are logical consequences of the input CNF.

- [RatTheory](RatTheory.v) defines and proves the verification of RAT clauses. RAT clauses are more general than RUP clauses in the sense than they may not be logical consequences of the input CNF. We prove here that extending a CNF with a bunch of RAT clauses preserves satisfiability of the CNF. 

- [RatProver](RatProver.v) defines and proves our RAT prover and its links with the external LRAT parser. The external LRAT parser aggregates RAT clauses by bunches: our LCF style requires to rebuild the dictionary of active clauses on each bunch. TODO: this whole rebuilt could probably be overcome by distinguishing clauses that do never interfer with any RAT pivot like in [GRAT](https://www21.in.tum.de/~lammich/grat).

- [SatAnsCert](SatAnsCert.v) is the main code.
