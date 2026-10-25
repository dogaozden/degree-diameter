#!/bin/bash
# fdcont.sh IN.sol OUT SEED CSECS CT0: continue the FLAGDEL coverage(+D1) annealing (dmhub2_t, targeted D1 moves)
IN=$1; O=$2; SD=$3; CS=${4:-300}; CT=${5:-0.12}
python3 ../hubs/sol2lift2.py "$IN" "${O}_in_l2.sol" > /dev/null
FREE="$(awk '$1=="free"{$1="";print}' "$IN")" H=3 FLAGDEL=1 HGFIRST=1 HGDIST=1 HUBG_IN="$IN" PHUB=0 HW=0 COVIT=999999999 \
  CSECS=$CS CT0=$CT ITERS=0 SEED=$SD SHOWUNC=1 timeout $((CS + 300)) nice -n 5 ./dmhub2_t gq/gq_q7.bin "${O}_in_l2.sol" "$O" > "$O.log" 2>&1
grep -E 'cover cost final|final cost' "$O.log"
