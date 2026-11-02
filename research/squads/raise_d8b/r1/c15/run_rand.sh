#!/bin/bash
BIN=/home/user/degree-diameter/research/frontier/raise_d8/bin
cd /home/user/degree-diameter/research/squads/raise_d8b/r1/c15
for s in "k7a 7 2 3 sl 29 883" "k7b 7 2 3 psl 41 631" "k5a 5 3 2 psl 89 61"; do
  set -- $s
  name=$1; k=$2; m=$3; f=$4; fam=$5; p=$6; n=$7
  ORBIT="$k $m $f" THREADS=1 RANDORB=16 nice -n 10 $BIN/haar_big0 17 8 60 1 8 /dev/null $fam $p $n > rand_$name.out 2> rand_$name.log
  echo "done $name" >> rand_progress.txt
done
echo ALLDONE >> rand_progress.txt
