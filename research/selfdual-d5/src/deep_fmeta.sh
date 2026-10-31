#!/bin/bash
# deep_fmeta.sh M KK R REC F MM SECS SEED: long sdtabu2 run on one record/type of C_M : C_KK (y x y^-1 = x^R), export
# cached in $TMPDIR/deep; output appended to logs/K$K/deep/f<M>_<KK>_<R>_r<REC>_f<F>.out (env K, NB, STALL, TABU).
R0="$(cd "$(dirname "$0")/.." && pwd)"; K=${K:-10}; T=${TMPDIR:-/tmp}/deep; mkdir -p $T $R0/logs/K$K/deep $R0/cand
M=$1; Q=$2; RR=$3; REC=$4; Fx=$5; Mx=$6; SECS=$7; SEED=$8; tag=${M}_${Q}_${RR}; [ -n "$SKIPA1" ] && tag=${tag}a; F=$T/f$tag.ht
# (SKIPA1=1: export without the a = 1 involutions, as the sweep did; record numbers must match the sweep's export)
EXT=""; [ $((K % 2)) -eq 0 ] && EXT=EXT
[ -s $F ] || SKIPA1=$SKIPA1 python3 $R0/src/meta_export.py $M $Q $RR $F $EXT > /dev/null
O=$R0/logs/K$K/deep/f${tag}_r${REC}_f${Fx}.out
echo "RUN seed $SEED secs $SECS NB ${NB:-96} STALL ${STALL:-2000} $(date -u +%H:%M)" >> $O
K=$K SECS=$SECS SEED=$SEED NB=${NB:-96} STALL=${STALL:-2000} MAXSOL=2 EDGES=$R0/cand/deep${K}_f${tag}_r${REC}_s$SEED.edges nice -n 5 $R0/src/${TABU:-sdtabu2} $F $REC $Fx $Mx >> $O 2>&1
if grep -q "^SOL" $O; then echo "HIT deep fmeta $((M * Q)) $tag rec $REC f $Fx" >> $R0/logs/K$K/HITS.txt; fi
