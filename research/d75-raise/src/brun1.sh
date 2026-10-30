#!/bin/bash
# brun1.sh N ID: exhaustive bi-coset search (|H| = |K| = 2) on SmallGroup(N,ID); logs logs/bic/N_ID.out, a line in logs/bsweep.txt
R="$(cd "$(dirname "$0")/.." && pwd)"; L=${LOGDIR:-$R/logs}; C=${CANDDIR:-$R/cand}; mkdir -p $L/bic $C
N=$1; ID=$2; T=${TMPDIR:-/tmp}/d75b; mkdir -p $T; F=$T/g${N}_${ID}.ht; t0=$(date +%s)
timeout ${GAPT:-900} gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";; NOAUT:=true;; INVS:=true;;" $R/src/export.g > /dev/null 2>&1
if [ ! -s $F ]; then echo "$N $ID GAPFAIL" >> $L/bsweep.txt; rm -f $F; exit 0; fi
EDGES=$C/bic_${N}_${ID}.edges timeout ${BICT:-3600} nice -n 5 $R/src/bic75 $F > $L/bic/${N}_${ID}.out 2>&1
rc=$?; sols=$(grep -c "^SOL" $L/bic/${N}_${ID}.out)
best=$(grep "^PAIR" $L/bic/${N}_${ID}.out | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}' | sort -n | head -1)
np=$(grep -c "^PAIR" $L/bic/${N}_${ID}.out); nc=$(grep -c CAPPED $L/bic/${N}_${ID}.out)
echo "$N $ID pairs $np capped $nc best ${best:-NA} sols $sols rc $rc secs $(( $(date +%s) - t0 ))" >> $L/bsweep.txt
[ "$sols" -gt 0 ] && echo "BICHIT $N $ID $sols" >> $L/HITS.txt
rm -f $F
