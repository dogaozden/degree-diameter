#!/bin/bash
# usage: run_anneal.sh OUTDIR SECS SEED < queue (one spec per line); 4 parallel, THREADS=1, nice
OUT=$1; SECS=$2; SEED=$3; mkdir -p $OUT
BIN=/tmp/claude-0/-home-user-degree-diameter/d68c5ced-3930-535c-a641-3fa3cd4e68f4/scratchpad/bin/haar_nm
job() { spec="$1"; tag=$(echo "$spec" | tr ' ' '_'); THREADS=1 nice timeout $(( ${SECS%.*} + 300 )) $BIN 4 10 $SECS $SEED 8 $OUT/sol_${tag}_s${SEED}.txt $spec > $OUT/log_${tag}_s${SEED}.txt 2>&1; echo -e "$spec\tseed=$SEED\t$(grep -o 'RESULT.*' $OUT/log_${tag}_s${SEED}.txt | tail -1)" >> $OUT/summary.tsv; }
export -f job; export OUT SECS SEED BIN
xargs -P 4 -I{} bash -c 'job "{}"'
echo ALLDONE >> $OUT/summary.tsv
