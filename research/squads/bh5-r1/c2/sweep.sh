#!/bin/bash
# usage: sweep.sh BASE SECS SEED OUTLOG GROUP_IDS... (group files groups/sg_<order>_<i>.txt given as order:i)
VL=/home/user/degree-diameter/research/beyond-haar-d5/vl
D=/home/user/degree-diameter/research/squads/bh5-r1/c2
BASE=$1; SECS=$2; SEED=$3; LOG=$4; shift 4
for oi in "$@"; do
  o=${oi%%:*}; i=${oi##*:}
  name=$(cat $D/groups/sg_${o}_${i}.name | cut -d' ' -f1-3)
  b=$(basename $BASE .base)
  res=$(cd $D && SECS=$SECS SEED=$SEED SWAP=0.05 T0=10 T1=0.5 OUT=$D/sols/${b}_${o}_${i}_s${SEED}.sol nice -n 10 timeout $((SECS+60)) $VL $BASE groups/sg_${o}_${i}.txt 2>/dev/null | grep RESULT)
  echo "$o $i [$name] $b s$SEED :: $res" >> $LOG
done
