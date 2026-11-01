#!/bin/bash
# run.sh SECS SEED n:lambda ... ; anneal Gray order-9 symmetric lift at D=16, logs RESULT lines to k02/runs.log
F=/home/user/degree-diameter/research/frontier; K=/home/user/degree-diameter/research/squads/beyond15/r3/k02
S=$1; SEED=$2; shift 2
cd $F/beyond15
for nl in "$@"; do n=${nl%%:*}; l=${nl#*:}
  tag=$K/g${n}_l${l}_s${SEED}
  r=$(timeout 100 env THREADS=1 T0=2.0 T1=0.05 L=1200 $F/bin/liftsym $F/beyond15/lsym/gray.txt $F/beyond15/lsym/gray.perm $n $l 16 $S $SEED $tag 2>/dev/null | grep RESULT)
  echo "$r" >> $K/runs.log; echo "$r"
done
