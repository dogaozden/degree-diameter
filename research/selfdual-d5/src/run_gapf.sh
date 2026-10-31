#!/bin/bash
# run_gapf.sh N TAG PRELUDE.g "GAP assignments": a formula group built in GAP by PRELUDE.g (e.g. src/affine_group.g
# with "P0:=11;; D0:=2;; K0:=20;; E0:=6;;"), exported by export_sd.g (full Aut(G); EXT records for even valency),
# sdtabu2 over every record and type (SECS, TYPES, NB, STALL, DEEP from the environment); one line in
# logs/K$K/gapf.txt, output logs/K$K/gapf/TAG.out.
R0="$(cd "$(dirname "$0")/.." && pwd)"
KV=${K:-10}; L=${LOGDIR:-$R0/logs/K$KV}; C=${CANDDIR:-$R0/cand}; mkdir -p $L/gapf $C
N=$1; tag=$2; PRE=$3; ARGS=$4; T=${TMPDIR:-/tmp}/sdg; mkdir -p $T
F=$T/g$tag.ht
t0=$(date +%s)
NOEXT="NOEXT:=1;;"; [ $((KV % 2)) -eq 0 ] && [ -z "$NOEXTEVEN" ] && NOEXT=""
cat $PRE $R0/src/export_sd.g > $T/run_$tag.g
timeout ${GAPT:-1800} nice gap -q -c "$ARGS OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > $L/gapf/$tag.gap 2>&1
rm -f $T/run_$tag.g
if [ ! -s $F ] || ! grep -q CENT $F; then echo "$N $tag GAPFAIL secs $(( $(date +%s) - t0 ))" >> $L/gapf.txt; rm -f $F; exit 0; fi
t1=$(date +%s)
K=$KV SECS=${SECS:-4} MAXSOL=${MAXSOL:-2} EDGES=$C/sdg${KV}_${tag}.edges timeout ${SDKT:-3600} nice -n 5 $R0/src/${TABU:-sdtabu2} $F all > $L/gapf/$tag.out 2>&1
rc=$?
O=$L/gapf/$tag.out
nty=$(grep -c "^TABU" $O); sols=$(grep -c "^SOL" $O)
best=$(grep "^TABU" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
echo "$N $tag K $KV types $nty best ${best:-NA} sols $sols rc $rc gap $(( t1 - t0 )) secs $(( $(date +%s) - t1 ))" >> $L/gapf.txt
[ "$sols" -gt 0 ] && echo "HIT gapf $N $tag K $KV $sols" >> $L/HITS.txt
[ "$sols" -gt 0 ] && cp $F $C/g${KV}_${tag}.ht
[ -n "$KEEP" ] && cp $F $KEEP/
rm -f $F
echo "$PRE|$ARGS" > $L/gapf/$tag.args
