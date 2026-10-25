#!/bin/bash
# usage: r3/batch.sh JOBFILE FLAGS SECONDS OUTDIR   (JOBFILE lines: "BASEFILE GROUPSPEC TAG"); 4 jobs at a time
JOBS=$1; FLAGS=$2; SECS=$3; OUT=$4; BIN=${BIN:-./ctrl_search}; mkdir -p $OUT
run() { b=$1; g=$2; tag=$3; timeout $((SECS+30)) nice -n 5 $BIN $b $g $FLAGS $SECS ${SEED:-1} $OUT/$tag > $OUT/$tag.out 2>&1; echo "$tag $(tail -n 1 $OUT/$tag.out | cut -c1-90)"; }
export -f run; export FLAGS SECS OUT BIN SEED
cat $JOBS | xargs -P ${PAR:-4} -L 1 bash -c 'run $0 $1 $2'
