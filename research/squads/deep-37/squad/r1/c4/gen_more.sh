#!/bin/bash
# gen_more.sh : few-orbit G-sets (CAP 40) for every SmallGroup of order 18, 24, 36 not yet done (background)
cd /home/user/degree-diameter/research/squads/deep-37
for n in 18 24 36; do
  for i in $(seq 1 $(echo "NrSmallGroups($n);" | gap -q 2>/dev/null | tr -d '\n ')); do
    [ -f squad/r1/c4/gs/n170/g${n}_${i}/est.txt ] && continue
    s=$(date +%s)
    timeout 300 bash squad/r1/c4/run_few.sh $n $i 170 $([ $n = 18 ] && echo 10 || ([ $n = 24 ] && echo 8 || echo 7)) 40
    echo "g${n}_${i} elapsed $(( $(date +%s) - s ))s"
  done
done
echo MORE_DONE
