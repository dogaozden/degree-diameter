#!/bin/bash
# farm_b3.sh S0 N : alternate SmallGroup(360,136) and (360,88), seeds S0..S0+N-1 each, d=6 D=5, 6 s per seed
cd $(dirname $0)
s0=$1; n=$2
for ((s=s0; s<s0+n; s++)); do
  for g in 136 88; do
    r=$(SAVEBEST=1 COOL=10 REHEAT=40 THREADS=1 timeout 40 nice -n 10 ../../tools/haar_tab 6 5 6 $s 16 s360_${g}_$s.sol tab g360_$g.bin 1 2>/dev/null | grep RESULT)
    echo "group=360_$g seed=$s $r" >> farm.log
  done
done
