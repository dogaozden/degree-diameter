#!/bin/bash
# h02 driver 2: chained scan links (START from the previous best voltages) on GP(10,3) n=283, then Pappus n=314 (N=5652)
H=/home/user/degree-diameter/research/squads/beyond13/r5/h02; B=/home/user/degree-diameter/research/frontier/beyond13
cd $H
START_F=out/n283s23.best
for k in 1 2 3 4 5 6; do
  seed=$((30+k))
  r=$(START=$START_F timeout 105 nice -n 10 ./scan bases/gp10_3.txt 283 14 95 $seed out/c283_$k 6 2>>out/drive2.err | grep RESULT)
  echo "gp10_3 n=283 chain$k START=$START_F $r" >> out/drive2.log
  case "$r" in *best=0\ *) timeout 60 nice -n 10 $B/bin/apsp out/c283_$k.edges 3 14 >> out/drive2.log 2>&1; cp out/c283_$k.edges sol/gp10_3_n283_D14_N5660.edges; echo FOUND >> out/drive2.log; break;; esac
  START_F=out/c283_$k.best
done
for seed in 41 42; do
  r=$(timeout 105 nice -n 10 ./scan bases/pappus18.txt 314 14 95 $seed out/pap314_$seed 6 2>>out/drive2.err | grep RESULT)
  echo "pappus n=314 seed=$seed $r" >> out/drive2.log
  case "$r" in *best=0\ *) timeout 60 nice -n 10 $B/bin/apsp out/pap314_$seed.edges 3 14 >> out/drive2.log 2>&1; cp out/pap314_$seed.edges sol/pappus_n314_D14_N5652.edges; echo FOUND >> out/drive2.log; break;; esac
done
echo DONE2 >> out/drive2.log
