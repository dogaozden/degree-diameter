#!/bin/bash
# run_c6.sh N ID : export SmallGroup(N,ID) with export3.g, run bic3 (sd mode, plus plain with a cap) on the
# non-normal order-3 subgroup classes, log one summary line to out/sweep.txt, keep solutions (edges) in out/.
C=/home/user/degree-diameter/research/squads/d75-r2/c6
N=$1; ID=$2; T=$C/tmp; mkdir -p $T $C/out
F=$T/g${N}_${ID}.bh
t0=$(date +%s)
timeout ${GAPT:-600} nice -n 15 gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";;" $C/src/export3.g < /dev/null > $T/gap_${N}_${ID}.log 2>&1
if [ ! -s $F ] || ! grep -q "^H " $F; then
  echo "{\"n\": $N, \"id\": $ID, \"status\": \"$( [ -s $F ] && echo no_order3_subgroups || echo gapfail)\"}" >> $C/out/sweep.txt; rm -f $F; exit 0; fi
EDGES=$C/out/bic_${N}_${ID}.edges MODE=${MODE:-sd} MAXEV=${MAXEV:-20000000} timeout ${BICT:-900} nice -n 15 $C/bic3 $F > $C/out/${N}_${ID}.out 2>&1
rc=$?
sols=$(grep -c "^SOL" $C/out/${N}_${ID}.out)
best=$(grep -E "^(SD|PLAIN) " $C/out/${N}_${ID}.out | sed -E 's/.*best ([0-9]+).*/\1/' | sort -n | head -1)
echo "{\"n\": $N, \"id\": $ID, \"Hclasses\": $(grep -c '^H ' $F), \"sols\": $sols, \"best\": \"${best:-NA}\", \"rc\": $rc, \"secs\": $(( $(date +%s) - t0 ))}" >> $C/out/sweep.txt
[ "$sols" -gt 0 ] && echo "HIT $N $ID $sols" >> $C/out/HITS.txt
rm -f $F
