#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r4/c3
for spec in "1,1,5 a" "0,1,6 b" "1,3,3 c" "2,2,3 d" "0,2,5 e"; do
  set -- $spec
  timeout 300 nice -n 10 python3 -I orbit7.py $1 $2 > orb_build_$2.log 2>&1
  if [ -f orbit7_graph_$2.bin ]; then
    timeout 200 nice -n 10 ./mis_csr orbit7_graph_$2.bin orb7_best_$2.txt 1 60 > orb7_run_$2.log 2>&1
  fi
done
echo ALLDONE > run_orbits.done
