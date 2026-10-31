#!/bin/bash
# run_fmeta.sh N M KK R: G = C_M : C_KK (y x y^-1 = x^R), GAP-free export (meta_export.py, EXT records for even
# valency), sdtabu2 (env TABU) over every record and type (SECS each, TYPES filter); one line in logs/K$K/fmeta.txt.
R0="$(cd "$(dirname "$0")/.." && pwd)"
KV=${K:-10}; L=${LOGDIR:-$R0/logs/K$KV}; C=${CANDDIR:-$R0/cand}; mkdir -p $L/fmeta $C
N=$1; M=$2; Q=$3; RR=$4; T=${TMPDIR:-/tmp}/sdf; mkdir -p $T
tag=${M}_${Q}_${RR}; F=$T/f$tag.ht
t0=$(date +%s)
EXT=""; [ $((KV % 2)) -eq 0 ] && EXT=EXT
python3 $R0/src/meta_export.py $M $Q $RR $F $EXT > $L/fmeta/$tag.exp 2>&1
if [ ! -s $F ]; then echo "$N $tag EXPFAIL" >> $L/fmeta.txt; exit 0; fi
t1=$(date +%s)
K=$KV SECS=${SECS:-4} MAXSOL=${MAXSOL:-2} EDGES=$C/sdf${KV}_${tag}.edges timeout ${SDKT:-3600} nice -n 5 $R0/src/${TABU:-sdtabu2} $F all > $L/fmeta/$tag.out 2>&1
rc=$?
O=$L/fmeta/$tag.out
nty=$(grep -c "^TABU" $O); sols=$(grep -c "^SOL" $O)
best=$(grep "^TABU" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
echo "$N $tag K $KV types $nty best ${best:-NA} sols $sols rc $rc exp $(( t1 - t0 )) secs $(( $(date +%s) - t1 ))" >> $L/fmeta.txt
[ "$sols" -gt 0 ] && echo "HIT fmeta $N $tag K $KV $sols" >> $L/HITS.txt
[ "$sols" -gt 0 ] && cp $F $C/f${KV}_${tag}.ht
[ -n "$KEEP" ] && cp $F $KEEP/
rm -f $F
[ -n "$SKIPA1" ] && touch $L/fmeta/$tag.skipa1
