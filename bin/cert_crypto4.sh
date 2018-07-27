#!/bin/bash
#
# tested with CryptoMiniSat version 4.5.3 (from http://baldur.iti.kit.edu/sat-competition-2016/solvers/main/cmsat5_main2.zip)

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_crypto4"
SOLVER="cryptominisat4_simple '${INPUT}' --drat='$(drat_file)'"

cert_solver "$@"
