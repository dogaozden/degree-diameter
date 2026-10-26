#!/bin/bash
# usage: run_long.sh OUTDIR SECS < lines "seed|spec" ; 4 parallel, THREADS=1, nice; uses haar_gen3 (split groups)
OUT=$1; SECS=$2; mkdir -p $OUT
BIN=/tmp/claude-0/-home-user-degree-diameter/d68c5ced-3930-535c-a641-3fa3cd4e68f4/scratchpad/bin/haar_gen3
job() { seed="${1%%|*}"; spec="${1#*|}"; tag=$(echo "$spec" | tr ' ' '_'); THREADS=1 nice timeout $(( SECS + 600 )) $BIN 4 10 $SECS $seed 8 $OUT/sol_${tag}_s${seed}.txt $spec > $OUT/log_${tag}_s${seed}.txt 2>&1; echo -e "$spec\tseed=$seed\t$(grep -o 'RESULT.*' $OUT/log_${tag}_s${seed}.txt | tail -1)" >> $OUT/summary.tsv; }
export -f job; export OUT SECS BIN
xargs -P 4 -I{} bash -c 'job "{}"'
echo ALLDONE >> $OUT/summary.tsv
