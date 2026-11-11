#!/bin/bash
BIN=/home/user/degree-diameter/research/frontier/raise_d8/bin
cd /home/user/degree-diameter/research/squads/raise_d8b/r1/c14
for s in "best1 sl 353 1" "best2 sl 151 13" "worst sl 29 1843"; do
  set -- $s
  name=$1; fam=$2; p=$3; n=$4
  ORBIT="3 6 1" THREADS=1 nice -n 10 $BIN/haar_big0 19 8 240 1 8 s_$name.sol $fam $p $n > s_$name.log 2>&1
  echo "done $name" >> search_progress.txt
done
echo ALLDONE >> search_progress.txt
