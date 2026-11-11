#!/bin/bash
# h02 driver: cost-0 search upward in n for the GP(10,3) lift (N = 20 n); stops after the first failure of every seed of n
H=/home/user/degree-diameter/research/squads/beyond13/r5/h02; B=/home/user/degree-diameter/research/frontier/beyond13
cd $H
for n in 283 284 285 286 287 288; do
  ok=0
  for seed in 21 22 23 24 25 26; do
    r=$(timeout 105 nice -n 10 ./scan bases/gp10_3.txt $n 14 95 $seed out/n${n}s$seed 6 2>>out/drive.err | grep RESULT)
    echo "n=$n seed=$seed $r" >> out/drive.log
    case "$r" in *best=0\ *)
      timeout 60 nice -n 10 $B/bin/apsp out/n${n}s$seed.edges 3 14 >> out/drive.log 2>&1
      cp out/n${n}s$seed.edges sol/gp10_3_n${n}_D14_N$((20*n)).edges; ok=1; break;;
    esac
  done
  [ $ok = 1 ] || break
done
echo DONE >> out/drive.log
