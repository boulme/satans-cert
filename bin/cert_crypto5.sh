#!/bin/bash

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_crypto5"
SOLVER="cryptominisat5_simple --drat=$(drat_file)"

cert_solver "$@"
