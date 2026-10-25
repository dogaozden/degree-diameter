#!/bin/bash
# Runs the remaining c5 groups one after another, each under the squad heavy lock (same command shape as the first run).
cd /home/user/degree-diameter/research/lowmem
OUT=../squads/d15D10-r2/c5
run() { # p n r
  local p=$1 n=$2 r=$3
  flock /tmp/claude-0/squad-heavy.lock timeout 300 nice -n 10 env ORBIT="15 1 0" AR=$r RANDORB=24 ./haar_lean 15 10 1 25 8 /dev/null psl $p $n > $OUT/rand_psl_${p}_${n}.txt 2>&1
  echo "finished psl $p $n exit=$?"
}
run 29 103951 38602
run 29 105691 79211
run 31 86491 39726
run 29 107581 82556
run 31 87991 78231
echo "ALL DONE"
