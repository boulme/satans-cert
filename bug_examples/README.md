# Bug Examples

File `test_v3_r8_vr5_c1_s8257.smt2-stp212.lrat` is an incorrect LRAT file (downloaded from [Peter Schneider-Kamp's page](http://imada.sdu.dk/~petersk/lrat/)) and generated from this [old version of `drat-trim`](https://imada.sdu.dk/~petersk/lrat/drat-trim.c). Hence, the following command is expected to fail.

    ../bin/satans-cert test_v3_r8_vr5_c1_s8257.smt2-stp212.cnf -l test_v3_r8_vr5_c1_s8257.smt2-stp212.lrat

This bug of `drat-trim` has been fixed. So, the following command should succeed (provided that `drat-trim` is up-to-date in the environment).

    ../bin/satans-cert test_v3_r8_vr5_c1_s8257.smt2-stp212.cnf -drat-file test_v3_r8_vr5_c1_s8257.smt2-stp212.drat


