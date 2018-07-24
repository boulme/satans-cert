#!/bin/bash
#
# tested with Maple_CM_Dist of SAT Competition 2018
#
# NB: the binary "glucose-static" built from "starexec_build"
#     is here renamed into "maple_cm_dist"

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_maple_cm_dist"
SOLVER="maple_cm_dist -drup-file=$(drat_file)"

cert_solver "$@"
