#!/bin/bash
# run1.sh N ID: export SmallGroup(N,ID) with GAP, run the exhaustive orbit-type Haar search, log one summary line.
# Output: logs/exh/N_ID.out (full), one line in logs/sweep.txt, first solution's edge list in cand/haar_N_ID.edges.
cd "$(dirname "$0")/.."
N=$1; ID=$2; T=${TMPDIR:-/tmp}/d75; mkdir -p $T
F=$T/g${N}_${ID}.ht
t0=$(date +%s)
timeout ${GAPT:-900} gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";;" src/export.g > /dev/null 2>&1
if [ ! -s $F ] || ! grep -q . $F; then echo "$N $ID GAPFAIL" >> logs/sweep.txt; rm -f $F; exit 0; fi
EDGES=cand/haar_${N}_${ID}.edges timeout ${EXHT:-1800} nice -n 5 src/haar75 $F exh > logs/exh/${N}_${ID}.out 2>&1
rc=$?
nal=$(grep -c "^TYPE" logs/exh/${N}_${ID}.out); sols=$(grep -c "^SOL" logs/exh/${N}_${ID}.out)
best=$(grep "^TYPE" logs/exh/${N}_${ID}.out | awk '{print $11}' | sort -n | head -1)
pass=$(grep "^TYPE" logs/exh/${N}_${ID}.out | awk '{s+=$17} END {print s+0}')
echo "$N $ID types $nal best ${best:-NA} passXX $pass sols $sols rc $rc secs $(( $(date +%s) - t0 ))" >> logs/sweep.txt
[ "$sols" -gt 0 ] && echo "HIT $N $ID $sols" >> logs/HITS.txt
rm -f $F
