#!/bin/bash
# run1.sh N ID: export SmallGroup(N,ID) with GAP, run the exhaustive orbit-type Haar search, log one summary line.
# Output: $L/exh/N_ID.out (full), one line in $L/sweep${X}.txt, first solution's edge list in $C/haar_N_ID.edges.
R="$(cd "$(dirname "$0")/.." && pwd)"
L=${LOGDIR:-$R/logs}; C=${CANDDIR:-$R/cand}; mkdir -p $L/exh $C
N=$1; ID=$2; MODE=${MODE:-exh}; X=$([ $MODE = exh ] && echo "" || echo "_$MODE"); T=${TMPDIR:-/tmp}/d75; mkdir -p $T
F=$T/g${N}_${ID}.ht
t0=$(date +%s)
timeout ${GAPT:-900} gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";;" $R/src/export.g > /dev/null 2>&1
if [ ! -s $F ] || ! grep -q . $F; then echo "$N $ID GAPFAIL" >> $L/sweep${X}.txt; rm -f $F; exit 0; fi
EDGES=$C/haar_${N}_${ID}${X}.edges timeout ${EXHT:-1800} nice -n 5 $R/src/haar75 $F $MODE > $L/exh/${N}_${ID}${X}.out 2>&1
rc=$?
nal=$(grep -c -E "^(TYPE|ANTI)" $L/exh/${N}_${ID}${X}.out); sols=$(grep -c "^SOL" $L/exh/${N}_${ID}${X}.out)
best=$(grep -E "^(TYPE|ANTI)" $L/exh/${N}_${ID}${X}.out | awk '{print $11}' | sort -n | head -1)
pass=$(grep -E "^(TYPE|ANTI)" $L/exh/${N}_${ID}${X}.out | awk '{s+=$17} END {print s+0}')
echo "$N $ID $MODE types $nal best ${best:-NA} passXX $pass sols $sols rc $rc secs $(( $(date +%s) - t0 ))" >> $L/sweep${X}.txt
[ "$sols" -gt 0 ] && echo "HIT $N $ID $sols" >> $L/HITS.txt
rm -f $F
