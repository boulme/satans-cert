#!/bin/bash

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_riss_bva"
SOLVER="riss -enabled_cp3 -up -subsimp -all_strength_res=3 -bva -bve -bve_red_lits=1 -no-bve_BCElim -unhide -cp3_uhdUHLE=0 -cp3_uhdIters=5 -drup=$(drat_file)"

cert_solver "$@"
