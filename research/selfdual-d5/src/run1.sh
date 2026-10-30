#!/bin/bash
# run1.sh N ID: export SmallGroup(N,ID) with GAP (export_sd.g), run sdk (valency K, default 6), log one summary line.
# Output: logs/K$K/out/N_ID.out (full), one line in logs/K$K/sweep.txt, first solution's edge list in cand/.
R="$(cd "$(dirname "$0")/.." && pwd)"
K=${K:-6}; L=${LOGDIR:-$R/logs/K$K}; C=${CANDDIR:-$R/cand}; mkdir -p $L/out $C
N=$1; ID=$2; T=${TMPDIR:-/tmp}/sdk; mkdir -p $T
F=$T/g${N}_${ID}.ht
t0=$(date +%s)
timeout ${GAPT:-900} gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";;" $R/src/export_sd.g > /dev/null 2>&1
if [ ! -s $F ] || ! grep -q CENT $F; then echo "$N $ID GAPFAIL secs $(( $(date +%s) - t0 ))" >> $L/sweep.txt; rm -f $F; exit 0; fi
t1=$(date +%s)
K=$K EDGES=$C/sd${K}_${N}_${ID}.edges timeout ${SDKT:-3600} nice -n 5 $R/src/sdk $F > $L/out/${N}_${ID}.out 2>&1
rc=$?
O=$L/out/${N}_${ID}.out
nty=$(grep -c "^TYPE" $O); sols=$(grep -c "^SOL" $O); ncap=$(grep "^TYPE" $O | grep -c CAPPED)
nrec=$(grep -E "^(ALPHA|EXT)" $F | wc -l); next=$(grep -c "^EXT" $F)
best=$(grep "^TYPE" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
pass=$(grep "^TYPE" $O | awk '{for(i=1;i<NF;i++) if ($i=="passXX") s+=$(i+1)} END {print s+0}')
echo "$N $ID K $K recs $nrec ext $next types $nty capped $ncap best ${best:-NA} passXX $pass sols $sols rc $rc gap $(( t1 - t0 )) secs $(( $(date +%s) - t1 ))" >> $L/sweep.txt
[ "$sols" -gt 0 ] && echo "HIT $N $ID K $K $sols" >> $L/HITS.txt
rm -f $F
