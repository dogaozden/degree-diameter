#!/bin/bash
# chain.sh Q START_BASE START_M MAXM SECS NSEED
# Warm-start chain on W(q) (c6, round 3): from a VALID Z_m design, map to Z_(m+1) by keeping every voltage (identity map)
# and run symrepair for SECS seconds (C-invariant, orbit sources). Up to NSEED seeds per step, all from the same Z_m base.
# A step counts as VALID only when the orbit-source run reaches 0 AND `baselift eval FILE 6` (all sources) prints
# VALID(all sources). The chain stops at the first step where no seed succeeds.
set -u
T=/home/user/degree-diameter/research/d16D8
D=/home/user/degree-diameter/research/squads/d16D8-r3/c6
Q=$1; BASE=$2; M=$3; MAXM=$4; SECS=$5; NSEED=$6; TAG=${7:-r}
SRC=$D/q$Q.src
LOG=$D/chain_q$Q.log
echo "== chain q=$Q tag=$TAG start=$BASE m=$M maxm=$MAXM secs=$SECS seeds=$NSEED $(date +%H:%M:%S)" >> "$LOG"
while [ "$M" -lt "$MAXM" ]; do
  NM=$((M+1))
  ok=0
  for s in $(seq 1 "$NSEED"); do
    IN=$D/q${Q}_${TAG}_m${NM}_from${M}_s${s}.base
    OUT=$D/q${Q}_${TAG}_m${NM}_s${s}_rep.base
    awk -v k="$NM" 'NR==1{$2=k} {print}' "$BASE" > "$IN"
    timeout 1500 nice -n 10 env THREADS=1 SRCFILE="$SRC" "$T/symrepair" "$IN" 6 "$SECS" $((1000*NM+s)) "$OUT" > "$OUT.log" 2>&1
    res=$(grep '^RESULT' "$OUT.log" | sed 's/.*best=\([0-9]*\).*/\1/')
    line=$(grep '^RESULT' "$OUT.log")
    echo "q=$Q m=$NM from=$M seed=$s orbit-best=${res:-NA} :: $line" >> "$LOG"
    if [ "${res:-x}" = "0" ]; then
      timeout 1500 nice -n 10 "$T/baselift" eval "$OUT" 6 > "$OUT.full" 2>&1
      fc=$(tail -1 "$OUT.full")
      echo "   full check: $fc" >> "$LOG"
      if grep -q 'VALID(all sources)' "$OUT.full"; then
        ok=1; BASE=$OUT; M=$NM
        echo "   VALID m=$NM (q=$Q) design=$OUT" >> "$LOG"
        break
      else
        echo "   WARNING: orbit-source 0 but full check not VALID" >> "$LOG"
      fi
    fi
  done
  if [ "$ok" -ne 1 ]; then
    echo "STOP q=$Q: no VALID seed at m=$NM (largest VALID so far m=$M, base=$BASE)" >> "$LOG"
    break
  fi
done
echo "END q=$Q largest VALID m=$M base=$BASE $(date +%H:%M:%S)" >> "$LOG"
