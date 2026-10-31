#!/bin/bash
# usage: run_sweep.sh OUTFILE "PSI indices" TYPES SECS GROUP...
S=/home/user/degree-diameter/research/selfdual-d6/src/sdhi
OUT=$1; PSIS=$2; TYPES=$3; SECS=$4; shift 4
: > "$OUT"
for i in $PSIS; do
  THREADS=1 ORDS=2,6 PSI=$i TYPES="$TYPES" SECS=$SECS MAXSOL=1 timeout 300 nice -n 10 $S 7 6 "$@" 2>&1 | grep -E "^(TABU|SOL|GROUP|PSI $i )|DONE" | sed "s/^/psi$i: /" >> "$OUT"
done
