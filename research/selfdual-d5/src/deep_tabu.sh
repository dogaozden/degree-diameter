#!/bin/bash
# deep_tabu.sh sg N ID REC F M SECS SEED   |   deep_tabu.sh meta N P K D REC F M SECS SEED   |   deep_tabu.sh meta2 N M K R REC F M SECS SEED
# Longer sdtabu run on one record/type of a group (export cached in $TMPDIR/deep); output appended to logs/K$K/deep/.
R="$(cd "$(dirname "$0")/.." && pwd)"; K=${K:-9}; T=${TMPDIR:-/tmp}/deep; mkdir -p $T $R/logs/K$K/deep $R/cand
NOEXT=""; [ $((K % 2)) -eq 1 ] && NOEXT="NOEXT:=1;;"
if [ $1 = sg ]; then N=$2; ID=$3; shift 3; tag=${N}_${ID}; F=$T/g$tag.ht
  [ -s $F ] || gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$F\";; $NOEXT" $R/src/export_sd.g > /dev/null 2>&1
elif [ $1 = meta2 ]; then N=$2; P=$3; Q=$4; D=$5; shift 5; tag=c${P}_${Q}_${D}; F=$T/$tag.ht
  if [ ! -s $F ]; then cat $R/src/meta_group2.g $R/src/export_sd.g > $T/run_$tag.g
    gap -q -c "M0:=$P;; K0:=$Q;; R0:=$D;; OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > /dev/null 2>&1; fi
else N=$2; P=$3; Q=$4; D=$5; shift 5; tag=${P}_${Q}_${D}; F=$T/m$tag.ht
  if [ ! -s $F ]; then cat $R/src/meta_group.g $R/src/export_sd.g > $T/run_$tag.g
    gap -q -c "P0:=$P;; K0:=$Q;; D0:=$D;; OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > /dev/null 2>&1; fi
fi
REC=$1; Fx=$2; Mx=$3; SECS=$4; SEED=$5
O=$R/logs/K$K/deep/${tag}_r${REC}_f${Fx}.out
K=$K SECS=$SECS SEED=$SEED MAXSOL=2 EDGES=$R/cand/deep${K}_${tag}_r${REC}_s$SEED.edges nice -n 5 $R/src/sdtabu $F $REC $Fx $Mx >> $O 2>&1
if grep -q "^SOL" $O; then echo "HIT deep $N $tag rec $REC f $Fx" >> $R/logs/K$K/HITS.txt; fi
