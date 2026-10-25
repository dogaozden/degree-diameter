#!/bin/bash
# usage: runq.sh N SPEC... (one job): anneal one candidate, log result line
N="$1"; shift; SEED="$1"; shift; SECS="$1"; shift; TAG="$1"; shift
SPEC="$*"
S=/tmp/claude-0/-home-user-degree-diameter/b452ef01-b49f-5c7b-990a-52fce27a99ee/scratchpad
TAGF=$(echo "$SPEC" | tr ' ' '_')
OUT=$S/sols/${TAG}_N${N}_${TAGF}_s${SEED}.txt
T0=$(date +%s)
R=$(THREADS=1 timeout $((SECS+200)) nice $S/haar_gen3 4 10 $SECS $SEED 8 $OUT $SPEC 2>&1)
BEST=$(echo "$R" | grep ^RESULT | grep -o 'best=[0-9?-]*' | head -1)
CHK=$(echo "$R" | grep -c "full diameter check: OK")
echo -e "run\t$N\t$SPEC\tseed=$SEED\t$BEST\tcheck=$CHK\t$(( $(date +%s)-T0 ))s" >> $S/logs/${TAG}.tsv
