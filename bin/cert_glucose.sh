#!/bin/bash
#
# tested with glucose 4.1 and 4.2.1

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_glucose"
SOLVER="glucose -certified -certified-output=$(drat_file) -model"

cert_solver "$@"
