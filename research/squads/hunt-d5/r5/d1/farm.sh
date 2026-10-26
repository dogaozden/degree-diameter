#!/bin/bash
# farm.sh SEED0 NSEEDS : haar_tab d=6 D=5 on SmallGroup(360,51) (table T.bin), 6 s per seed, one process at a time
s0=$1; ns=$2
for ((s=s0; s<s0+ns; s++)); do
  r=$(SAVEBEST=1 COOL=10 REHEAT=40 THREADS=1 timeout 26 nice -n 10 ../../tools/haar_tab 6 5 6 $s 16 s$s.sol tab T.bin 1 2>/dev/null | grep RESULT)
  echo "seed=$s $r" >> farm.log
done
echo DONE$s0 >> farm.log
