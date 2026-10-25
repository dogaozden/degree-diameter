#!/bin/bash
# fdrun.sh IN.sol "FDSET" OUT SEED CSECS CT0 [HUBIN]: per-flag FLAGDEL coverage(+D1) annealing with dmhub2_f.
# IN must be in H=3 numbering (mkhubF.py output or an earlier fdrun output).
IN=$1; FS=$2; O=$3; SD=$4; CS=${5:-300}; CT=${6:-0.2}
python3 ../hubs/sol2lift2.py "$IN" "${O}_in_l2.sol" > /dev/null
FREE="$(awk '$1=="free"{$1="";print}' "$IN")" H=3 FLAGDEL=1 FDSET="$FS" HGFIRST=1 HGDIST=1 HUBG_IN="$IN" PHUB=0 HW=0 \
  COVIT=999999999 CSECS=$CS CT0=$CT ITERS=0 SEED=$SD SHOWUNC=1 timeout $((CS + 300)) nice -n 5 ./dmhub2_f gq/gq_q7.bin "${O}_in_l2.sol" "$O" > "$O.log" 2>&1
grep -E 'cover cost final|final cost' "$O.log"
