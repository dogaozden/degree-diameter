#!/bin/bash
# run_tabu.sh N ID: export SmallGroup(N,ID) (no EXT records for odd K), run sdtabu over every record and type
# (SECS each, TYPES filter), one line in logs/K$K/tabu.txt; first solution's edge list in cand/.
R="$(cd "$(dirname "$0")/.." && pwd)"
K=${K:-9}; L=${LOGDIR:-$R/logs/K$K}; C=${CANDDIR:-$R/cand}; mkdir -p $L/tabu $C
N=$1; ID=$2; T=${TMPDIR:-/tmp}/sdt; mkdir -p $T
F=$T/g${N}_${ID}.ht
t0=$(date +%s)
NOEXT=""; [ $((K % 2)) -eq 1 ] && NOEXT="NOEXT:=1;;"
timeout ${GAPT:-1200} gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";; $NOEXT" $R/src/export_sd.g > /dev/null 2>&1
if [ ! -s $F ] || ! grep -q CENT $F; then echo "$N $ID GAPFAIL secs $(( $(date +%s) - t0 ))" >> $L/tabu.txt; rm -f $F; exit 0; fi
t1=$(date +%s)
K=$K SECS=${SECS:-4} MAXSOL=${MAXSOL:-2} EDGES=$C/sdt${K}_${N}_${ID}.edges timeout ${SDKT:-3600} nice -n 5 $R/src/${TABU:-sdtabu} $F all > $L/tabu/${N}_${ID}.out 2>&1
rc=$?
O=$L/tabu/${N}_${ID}.out
nty=$(grep -c "^TABU" $O); sols=$(grep -c "^SOL" $O)
best=$(grep "^TABU" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
echo "$N $ID K $K types $nty best ${best:-NA} sols $sols rc $rc gap $(( t1 - t0 )) secs $(( $(date +%s) - t1 ))" >> $L/tabu.txt
[ "$sols" -gt 0 ] && echo "HIT $N $ID K $K $sols" >> $L/HITS.txt
rm -f $F
