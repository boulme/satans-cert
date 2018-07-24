#!/bin/bash
#
# tested with the CaDiCaL of SAT Competition 2018

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_cadical"
SOLVER="cadical - $(drat_file)"

cert_solver "$@"
