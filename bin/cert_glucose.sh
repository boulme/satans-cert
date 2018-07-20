#!/bin/bash

mydir="$(cd "$(dirname $0)"; pwd)"

source "${mydir}/default_config.sh"

PREFIX="${PREFIX}_glucose"
SOLVER="glucose -certified -certified-output=$(drat_file) -model"

cert_solver "$@"
