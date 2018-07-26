# Bash library that defines a "cert_solver" function which wraps calls to "satans-cert" with default values...
# See example in cert_glucose.sh

myself="$(basename $0)"
mydir="$(cd "$(dirname $0)"; pwd)"

die() {
    echo "ERROR: $@" 1>&2
    echo 1>&2  
    echo "NB: ${myself} has the same command-line than satans-cert (see below)" 1>&2  
    echo "except that *.cnf.bz2 are also supported in input." 1>&2  
    echo 1>&2  
    ${mydir}/satans-cert -help 1>&2   
    exit 1
}

tmp_name() {
    echo "/tmp/$(basename $1)_$$.cnf"
}

cleaning() {
    if [ "x${TMP}" != "x" ]; then
        rm -f "${TMP}" && echo "* ${TMP} removed !"
    fi
}

# trap Ctrl+C to perform cleaning...
trap 'cleaning; exit 1' INT

# DEFAULT INITIALIZATIONS

DRATTRIM="drat-trim"
INPUT="$1"
TMP=""

if [ -f "${INPUT}" ]; then
    PREFIX="${INPUT%.cnf*}" # default prefix
    case "${INPUT}" in
        # TODO: consider other compression format ?
        *.bz2 | *.bzip2 )
            TMP="$(tmp_name ${PREFIX})"
            echo "* found a bzip2 file: starting decompression in ${TMP}"
            bzip2 -c -d "${INPUT}" > "${TMP}" || exit 1
            echo "* size(kB;vars;clauses):$(du -ks ${TMP} | awk -F ' ' -e '{print $1}');$(grep -e '^p cnf' ${TMP} | awk -F ' ' -e '{print $3";"$4}')"
            INPUT="${TMP}"
            ;;
    esac
    shift
else
    die "the first argument \"${INPUT}\" is not an existing file (expects a .cnf or .cnf.bz2 file)"
    exit 1
fi

# functions

drat_file() {
    echo "${PREFIX}.drat"
}

cert_solver(){
    ${mydir}/satans-cert "${INPUT}"  -s "${SOLVER}" -d "${DRATTRIM}" -outfile "${PREFIX}.out" -drat-file "$(drat_file)" -lrat-file "${PREFIX}.lrat" "$@"
    cleaning
}
