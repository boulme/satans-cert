# SatAns-Cert (Certifying Answers of Boolean SAT-Solvers)

We provide an [OCaml](http://ocaml.org/) wrapper certified in [Coq](https://coq.inria.fr/) to check answers of state-of-the-art SAT-solvers.
On UNSAT answers, our wrapper checks lrat certificates generated by [drat-trim](https://github.com/marijnheule/drat-trim).

The design of our certified checker exploits a parametricity property of ML polymorphic types in order to keep the Coq code as lightweight as possible.
See details in our [slides from the Coq workshop 2018](https://coqworkshop2018.inria.fr/files/2018/07/coq2018_talk_boulme.pdf).
This technique is provided by our [Impure](coq_src/Impure) library, itself inspired from the [Verified Polyhedra Library](https://github.com/VERIMAG-Polyhedra/VPL). Actually, we wish to put this Impure library in a separate repository. But this would currently be rather inconvenient because of the lack of a "Separate Extraction" in Coq that is truly compatible with OCaml separate compilation, see feature wish [coq#8042](https://github.com/coq/coq/issues/8042).

## CREDITS

[Sylvain Boulmé](mailto:Sylvain.Boulme@univ-grenoble-alpes.fr) and Thomas Vandendorpe from [Verimag](http://www-verimag.imag.fr/), supported by [ERC Stator](http://stator.imag.fr/w/index.php/Main_Page)
led by [David Monniaux](http://www-verimag.imag.fr/~monniaux/).

## COMPILATION

    make -C ocaml/

## USAGE

    bin/satans-cert -help

See also bash scripts in [bin/](https://github.com/boulme/satans-cert/tree/master/bin) to wrap a given sat solver

## CODE OVERVIEW

The main code of `santans-cert` is defined in [SatAnsCert.v](coq_src/SatAnsCert.v) together with its partial correctness proof, see [coq_src/](coq_src/) for details.

- [coq_src/](coq_src) contains all our Coq sources, including the [Impure](coq_src/Impure) library as a subdirectory and the OCaml oracles of this library.

- [ocaml/](ocaml) contains our OCaml oracles for `satans-cert`.

- [examples/](examples) contains CNF examples in DIMACS format.

- [bin/](bin) contains scripts to wrap `satans-cert` options.

- [FibExample_build/](FibExample_build) is a "build" directory for source file [FibExample.v](coq_src/Impure/FibExample.v). It illustrates another application of our Impure library: how to "certify for free" an external generic memoizing fixpoint operator, ie by using only its polymorphic ML type + a bit of defensive checks.
