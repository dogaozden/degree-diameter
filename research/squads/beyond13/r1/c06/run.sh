#!/bin/bash
# run.sh fam p n seed seconds [START]  -- one haar_big0 run at (4,14), ORBIT "3 1 1", K=8, THREADS=1
B=/home/user/degree-diameter/research/frontier/beyond13
C=/home/user/degree-diameter/research/squads/beyond13/r1/c06
fam=$1; p=$2; n=$3; seed=$4; secs=$5; start=$6
stem=d4D14_${fam}_${p}_${n}_orb3-1-1_s${seed}
cd $C/runs
if [ -n "$start" ]; then
  START=$start ORBIT="3 1 1" THREADS=1 timeout 105 nice -n 10 $B/bin/haar_big0 4 14 $secs $seed 8 $C/runs/$stem.out $fam $p $n > $C/runs/$stem.log 2>&1
else
  ORBIT="3 1 1" THREADS=1 timeout 105 nice -n 10 $B/bin/haar_big0 4 14 $secs $seed 8 $C/runs/$stem.out $fam $p $n > $C/runs/$stem.log 2>&1
fi
echo "$fam $p $n seed=$seed rc=$? $(grep RESULT $C/runs/$stem.log | tail -1)"
