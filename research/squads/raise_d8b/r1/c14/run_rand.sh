#!/bin/bash
BIN=/home/user/degree-diameter/research/frontier/raise_d8/bin
cd /home/user/degree-diameter/research/squads/raise_d8b/r1/c14
for s in "A psl 449 1" "B psl 191 13" "C psl 83 157" "D psl 41 1303" "E sl 353 1" "F sl 151 13" "G sl 53 301" "H sl 29 1843"; do
  set -- $s
  name=$1; fam=$2; p=$3; n=$4
  ORBIT="3 6 1" THREADS=1 RANDORB=30 nice -n 10 $BIN/haar_big0 19 8 60 1 8 /dev/null $fam $p $n > rand_$name.out 2> rand_$name.log
  echo "done $name" >> rand_progress.txt
done
echo ALLDONE >> rand_progress.txt
