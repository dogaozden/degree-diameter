#!/bin/bash
# batch over SmallGroups of orders 1971..2000 divisible by 3 (sd mode), sequential
C=/home/user/degree-diameter/research/squads/d75-r2/c6
for n in $(seq 1971 2000); do
  [ $((n % 3)) -eq 0 ] || continue
  k=$(timeout 60 gap -q -c "Print(NrSmallGroups($n)); QUIT;" < /dev/null 2>/dev/null | tail -1)
  for i in $(seq 1 $k); do
    GAPT=300 BICT=300 MODE=sd MAXEV=20000000 $C/src/run_c6.sh $n $i
  done
done
echo BATCHDONE >> $C/out/sweep.txt
