#!/bin/bash
# usage: verify.sh BASENAME N I v1 v2 ... (free voltages from a cost-0 lanneal run)
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c3
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c3/tmp
export THREADS=1
b=$1; n=$2; i=$3; shift 3
cd /home/user/degree-diameter/research/theorems/smallfam
timeout 600 nice -n 10 python3 lift_edges.py $n $i bases/$b.txt "$OUTDIR/lift_${b}_${n}_${i}.edges" "$@" && \
timeout 600 nice -n 10 ./verify/apsp "$OUTDIR/lift_${b}_${n}_${i}.edges" 3 10
