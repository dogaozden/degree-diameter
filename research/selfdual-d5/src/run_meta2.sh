#!/bin/bash
# run_meta2.sh N M K R: G = C_M : C_K, y x y^-1 = x^R (meta_group2.g), export (meta_group.g + export_sd.g), sdtabu over every
# record and type; one line in logs/K$KV/meta.txt (KV = valency, env K).
R="$(cd "$(dirname "$0")/.." && pwd)"
KV=${K:-9}; L=${LOGDIR:-$R/logs/K$KV}; C=${CANDDIR:-$R/cand}; mkdir -p $L/meta2 $C
N=$1; P=$2; Q=$3; D=$4;  # here P = M, D = R T=${TMPDIR:-/tmp}/sdm; mkdir -p $T
F=$T/m${P}_${Q}_${D}.ht; tag=${P}_${Q}_${D}
t0=$(date +%s)
NOEXT=""; [ $((KV % 2)) -eq 1 ] && NOEXT="NOEXT:=1;;"
cat $R/src/meta_group2.g $R/src/export_sd.g > $T/run_$tag.g
timeout ${GAPT:-1200} gap -q -c "M0:=$P;; K0:=$Q;; R0:=$D;; OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > /dev/null 2>&1
rm -f $T/run_$tag.g
if [ ! -s $F ] || ! grep -q CENT $F; then echo "$N $tag GAPFAIL secs $(( $(date +%s) - t0 ))" >> $L/meta2.txt; rm -f $F; exit 0; fi
t1=$(date +%s)
K=$KV SECS=${SECS:-4} MAXSOL=${MAXSOL:-2} EDGES=$C/sdc${KV}_${tag}.edges timeout ${SDKT:-3600} nice -n 5 $R/src/sdtabu $F all > $L/meta2/$tag.out 2>&1
rc=$?
O=$L/meta2/$tag.out
nty=$(grep -c "^TABU" $O); sols=$(grep -c "^SOL" $O)
best=$(grep "^TABU" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
echo "$N $tag K $KV types $nty best ${best:-NA} sols $sols rc $rc gap $(( t1 - t0 )) secs $(( $(date +%s) - t1 ))" >> $L/meta2.txt
[ "$sols" -gt 0 ] && echo "HIT meta2 $N $tag K $KV $sols" >> $L/HITS.txt
[ "$sols" -gt 0 ] && cp $F $C/c${KV}_${tag}.ht
rm -f $F
