#!/bin/bash
# Pass 1 driver for card c7 (bicay SA sweep). Idempotent: skips (file,a,b) already in pass1.tsv.
# usage: pass1.sh DEADLINE_EPOCH
C7=/home/user/degree-diameter/research/squads/s65r3/c7
BC=/home/user/degree-diameter/research/s65/groups/bc
BIN=/home/user/degree-diameter/research/s65/tools/bicay
DEADLINE=$1
OUT=$C7/pass1.tsv
[ -f $OUT ] || printf "file\ta\tb\tcost\tsec\n" > $OUT
COMBOS=("2 4" "4 2" "3 3" "1 5" "5 1")
cd $BC || exit 1
run() { # file a b
  local f=$1 a=$2 b=$3
  if grep -q -P "^$(basename $f)\t$a\t$b\t" $OUT 2>/dev/null; then return; fi
  if [ $(date +%s) -gt $DEADLINE ]; then return 1; fi
  local t0=$(date +%s.%N) full res cost
  full=$(A=$a B=$b MODE=sa SECS=4 SEED=1 timeout 60 nice -n 10 $BIN $f 2>/dev/null)
  res=$(echo "$full" | grep '^RESULT')
  cost=$(echo "$res" | sed -n 's/^RESULT best \(-\?[0-9]*\).*/\1/p')
  [ -z "$cost" ] && cost=$(echo "$res" | grep -q skipped && echo skip || echo err)
  local dt=$(echo "$(date +%s.%N) - $t0" | bc)
  printf "%s\t%s\t%s\t%s\t%.1f\n" "$(basename $f)" $a $b "$cost" "$dt" >> $OUT
  if echo "$res" | grep -q 'sols [1-9]'; then
    echo "COST0 $(basename $f) $a $b" >> $C7/cost0.txt; echo "$full" >> $C7/cost0_sols.txt; fi
  return 0
}
# Phase A: orders 344-350 (41 files) with (2,4) and (3,3)
for f in $(ls bc_34[4-9]_*.txt bc_350_*.txt | sort); do
  for c in "2 4" "3 3"; do set -- $c; run $BC/$f $1 $2 || exit 0; done
done
# Phase B: orders 354, 356, 358 (8 files), rotating combos
k=0
for f in $(ls bc_35[468]_*.txt | sort); do
  set -- ${COMBOS[$((k % 5))]}; run $BC/$f $1 $2 || exit 0; k=$((k+1))
done
# Phase C: random sample of 352 and 360 files, one rotating combo per file
for f in $(ls bc_352_*.txt bc_360_*.txt | shuf --random-source=<(yes 7)); do
  set -- ${COMBOS[$((k % 5))]}; run $BC/$f $1 $2 || exit 0; k=$((k+1))
done
echo DONE
