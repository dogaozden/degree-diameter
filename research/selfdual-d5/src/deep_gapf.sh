#!/bin/bash
# deep_gapf.sh TAG PRELUDE.g "GAP assignments" REC F MM SECS SEED: long sdtabu run on one record/type of a formula group
# built in GAP (as in run_gapf.sh; export cached in $TMPDIR/deep); output appended to logs/K$K/deep/TAG_r<REC>_f<F>.out.
R0="$(cd "$(dirname "$0")/.." && pwd)"; K=${K:-9}; T=${TMPDIR:-/tmp}/deep; mkdir -p $T $R0/logs/K$K/deep $R0/cand
tag=$1; PRE=$2; ARGS=$3; REC=$4; Fx=$5; Mx=$6; SECS=$7; SEED=$8; F=$T/g$tag.ht
NOEXT="NOEXT:=1;;"; [ $((K % 2)) -eq 0 ] && NOEXT=""
if [ ! -s $F ]; then cat $R0/$PRE $R0/src/export_sd.g > $T/run_$tag.g
  nice gap -q -c "$ARGS OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > /dev/null 2>&1; rm -f $T/run_$tag.g; fi
O=$R0/logs/K$K/deep/${tag}_r${REC}_f${Fx}.out
echo "RUN seed $SEED secs $SECS NB ${NB:-96} STALL ${STALL:-2000} ENDG ${ENDG:-0} $(date -u +%H:%M)" >> $O
K=$K SECS=$SECS SEED=$SEED NB=${NB:-96} STALL=${STALL:-2000} MAXSOL=2 EDGES=$R0/cand/deep${K}_${tag}_r${REC}_s$SEED.edges nice -n 5 $R0/src/${TABU:-sdtabu2} $F $REC $Fx $Mx >> $O 2>&1
if grep -q "^SOL" $O; then echo "HIT deep gapf $tag rec $REC f $Fx" >> $R0/logs/K$K/HITS.txt; fi
