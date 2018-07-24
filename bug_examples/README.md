# Bug Examples

File `test_v3_r8_vr5_c1_s8257.smt2-stp212.lrat` is an incorrect LRAT file generated from an old version of `drat-trim`
(downloaded from [this page](http://imada.sdu.dk/~petersk/lrat/)). Hence, the following command is expected to fail.

    ../bin/satans-cert test_v3_r8_vr5_c1_s8257.smt2-stp212.cnf -l test_v3_r8_vr5_c1_s8257.smt2-stp212.lrat

This bug of `drat-trim` has been fixed. So, the following command should succeed (provided that `drat-trim` is up-to-date in the environment).

    ../bin/satans-cert test_v3_r8_vr5_c1_s8257.smt2-stp212.cnf -drat-file test_v3_r8_vr5_c1_s8257.smt2-stp212.drat


