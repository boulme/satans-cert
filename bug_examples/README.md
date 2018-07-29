# Bug Examples

## Incorrect LRAT proof

File `test_v3_r8_vr5_c1_s8257.smt2-stp212.lrat` is an incorrect LRAT file (downloaded from [Peter Schneider-Kamp's page](http://imada.sdu.dk/~petersk/lrat/)) and generated from this [old version of `drat-trim`](https://imada.sdu.dk/~petersk/lrat/drat-trim.c). Hence, the following command is expected to fail.

    ../bin/satans-cert test_v3_r8_vr5_c1_s8257.smt2-stp212.cnf -l test_v3_r8_vr5_c1_s8257.smt2-stp212.lrat

This bug of `drat-trim` has been fixed. So, the following command should succeed (provided that `drat-trim` is up-to-date in the environment) to produce a certified 'UNSAT !' answer.

    ../bin/satans-cert test_v3_r8_vr5_c1_s8257.smt2-stp212.cnf -drat-file test_v3_r8_vr5_c1_s8257.smt2-stp212.drat

## Incorrect UNSAT answer

Occasionally, some SAT-solvers give incorrect answers in SAT competition (and thus get disqualified). For example, from the parallel track of [SAT competition 2017](https://baldur.iti.kit.edu/sat-competition-2017/index.php?cat=results), it appears that solver [abcdsat\_p](https://baldur.iti.kit.edu/sat-competition-2017/solvers/parallel/abcdsat_parallel.zip) answers 'UNSATISFIABLE' on the 'mp1-9\_38.cnf' file of the [benchmark](https://baldur.iti.kit.edu/sat-competition-2017/benchmarks/Main.zip). Here, no DRAT proof is given, because it was only required in the main track. But, this 'mp1-9\_38.cnf' is proved 'SAT !' by using [CaDiCaL+satans-cert](../bin/cert_cadical.sh).

