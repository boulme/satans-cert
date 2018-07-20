# Bash library that defines a "cert_solver" function which wraps calls to "satans-cert" with default values...
# See example in cert_glucose.sh

myself="$(basename $0)"
mydir="$(cd "$(dirname $0)"; pwd)"

die() {
    echo "ERROR: $@" 1>&2
    echo "NB: ${myself} has the same command-line than satans-cert (see below)" 1>&2  
    echo 1>&2  
    ${mydir}/satans-cert -help 1>&2   
    exit 1
}

# trap Ctrl+C (otherwise, only subprocessed will be trapped)

trap 'echo " bye!"; exit 1' INT

# DEFAULT INITIALIZATIONS

DRATTRIM="drat-trim"
INPUT="$1"

if [ -f "${INPUT}" ]; then
    PREFIX="${INPUT%.cnf}" # default prefix
    shift
else
    die "the first argument \"${INPUT}\" is not an existing file (expects a .cnf file)"
    exit 1
fi

# functions

drat_file() {
    echo "${PREFIX}.drat"
}

cert_solver(){
    ${mydir}/satans-cert "${INPUT}"  -s "${SOLVER}" -d "${DRATTRIM}" -outfile "${PREFIX}.out" -drat-file "$(drat_file)" -lrat-file "${PREFIX}.lrat" "$@"
}
