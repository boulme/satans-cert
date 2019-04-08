# SatAns-Cert (Certifying Answers of Boolean SAT-Solvers)

We provide an [OCaml](http://ocaml.org/) wrapper certified in [Coq](https://coq.inria.fr/) to check answers of state-of-the-art SAT-solvers.
On UNSAT answers, our wrapper checks LRAT certificates generated by [drat-trim](https://github.com/marijnheule/drat-trim).
Actually, we have been inspired by the ["Efficient Certified RAT Verification" paper](https://imada.sdu.dk/~petersk/lrat).

Our main contribution is to base the design of our certified checker on a [parametricity](http://homepages.inf.ed.ac.uk/wadler/topics/parametricity.html) property of ML polymorphic types, in order to keep the Coq code as lightweight as possible.
See details in our [slides from the Coq workshop 2018](https://coqworkshop2018.inria.fr/files/2018/07/coq2018_talk_boulme.pdf).
This technique is provided by our [Impure](https://github.com/boulme/Impure) library located here at [coq_src/Impure/](coq_src/Impure/) as a [git-subrepo](https://github.com/ingydotnet/git-subrepo). Actually, we wish to put this `Impure` library as a true separate library. But this would currently be rather inconvenient because of the lack of a "Separate Extraction" in Coq that is truly compatible with OCaml separate compilation, see feature wish [coq#8042](https://github.com/coq/coq/issues/8042).

See [our draft paper on this work](https://hal.archives-ouvertes.fr/hal-02062288).

## Credits

[Sylvain Boulmé](mailto:Sylvain.Boulme@univ-grenoble-alpes.fr) and Thomas Vandendorpe from [Verimag](http://www-verimag.imag.fr/), supported by [ERC Stator](http://stator.imag.fr/w/index.php/Main_Page)
led by [David Monniaux](http://www-verimag.imag.fr/~monniaux/).

## Installation

### Requirements

1. [ocaml](https://ocaml.org/docs/install.html). Tested with versions >= 4.05 and <= 4.07.1. (But other versions should work too).

2. [ocamlbuild](https://github.com/ocaml/ocamlbuild). Tested with version 0.12.0 abd 0.14.0. (But other versions should work too).

3. [coq](https://coq.inria.fr/). Tested with versions >= 8.7.2 and <= 8.9.0. Here, other versions are likely to not work !

### Compilation of `satans-cert`

From the root of the repository, simply run:

    make -C ocaml/

NB: this first compiles the Coq sources and extract them in `ocaml/coq_extracted` before running `ocamlbuild`.

Then, if you want to test than everything is ok, run:

    make -C examples/

### Optional installation of `drat-trim`

Simply clone and `make` the [drat-trim repository](https://github.com/marijnheule/drat-trim).
Then make `drat-trim` executable known from your PATH.

NB: `drat-trim` is needed to produce LRAT proofs from DRAT proofs produced by state-of-the-art SAT-solvers.

### Optional installation of state-of-the-art SAT-solvers

We have tried several state-of-the-art SAT-solvers like [CaDiCaL](http://fmv.jku.at/cadical/), [CryptoMinisat 4.5.3](http://baldur.iti.kit.edu/sat-competition-2016/solvers/main/cmsat5_main2.zip), [CryptoMinisat 5](https://github.com/msoos/cryptominisat), [Glucose 4](http://www.labri.fr/perso/lsimon/glucose/) or [Riss 4.27](http://tools.computational-logic.org/content/riss.php).

The simplest way is to download directly the source of such SAT solvers from the [SAT competition](http://www.satcompetition.org/) pages, like
 [the SAT Competition 2018 page](http://sat2018.forsyte.tuwien.ac.at/index.php?cat=solvers).
Then make these executables known from your PATH.

NB: in our experiments, [CryptoMinisat 4.5.3](http://baldur.iti.kit.edu/sat-competition-2016/solvers/main/cmsat5_main2.zip) and [Riss 4.27](http://tools.computational-logic.org/content/riss.php) have been the only solvers to produce non-RUP RAT clauses. All others have only produced DRUP proofs.

## Usage


        satans-cert <input.cnf> [ <OPTION> ... ]

    where <input.cnf> is a file in DIMACS format

    -l [LRAT_FILE] 	 just check LRAT_FILE

    -s [SOLVER] where SOLVER is the command running the solver:
        solver's input is given on standard input (in DIMACS format)
	    solver's answer has to be on standard output (in DIMACS format)
	    solver's DRAT proof has to be in a file named "proof.out" 
		    or which named is given with -drat-file option
	NB: if SOLVER is the empty string (default case) then DRATTRIM is attempted on DRAT_FILE

    -outfile [DIMACS_OUT_FILE] 	 name of the auxiliary DIMACS FILE OUTPUT from the sat solver 

    -d [DRATTRIM] 	 where DRATTRIM is the command running drat-trim (default is "drat-trim")

    -drat-file [DRAT_FILE] 	 name of the auxiliary DRAT_FILE 

    -lrat-file [LRAT_FILE] 	 name of the auxiliary LRAT_FILE 

    -f 	 force recomputation and remove generated auxiliary files (default)

    -lazy 	 skip recomputation if auxiliary file exists, and preserve these files anyway

    -help  Display this list of options


See also bash scripts in [bin/](https://github.com/boulme/satans-cert/tree/master/bin) to wrap a given sat solver,
or direct invocations in [bug_examples/](bug_examples) and [examples/Makefile](examples/Makefile).

## Code Overview

The main code of `santans-cert` is defined in [SatAnsCert.v](coq_src/SatAnsCert.v) together with its partial correctness proof, see [coq_src/README](coq_src/) for details.

- [coq_src/](coq_src) contains all our Coq sources, including the [Impure](coq_src/Impure) library as a subdirectory and the OCaml oracles of this library.

- [ocaml/](ocaml) contains our OCaml oracles for `satans-cert`.

- [bug_examples/](bug_examples) contains examples using `satans-cert`.

- [examples/](examples) contains other CNF examples in DIMACS format.
Moreover, file [sudoku9-s1.out](examples/sudoku9-s1.out) gives the model (in DIMACS format) of [sudoku9-s1.cnf](examples/sudoku9-s1.cnf) found by [CaDiCaL](http://fmv.jku.at/cadical/).
At last, file [sudoku9-1.lrat](examples/sudoku9-1.lrat) gives a UNSAT proof (in LRAT format) of [sudoku9-1.cnf](examples/sudoku9-1.cnf) found from the DRAT proof of [CaDiCaL](http://fmv.jku.at/cadical/)
by [drat-trim](https://www.cs.utexas.edu/~marijn/drat-trim/).

- [bin/](bin) contains scripts to wrap `satans-cert` options.
