#!/bin/bash
# sequential full K=3 enumerations of triples of implicated free edges around start_s8.sol (cost 4)
cd /home/user/degree-diameter/research/squads/s384r2/c4
for T in 1,4,7 1,4,5 1,5,7 4,5,7; do
  tag=$(echo $T | tr , _)
  PLAT=plat_$tag.txt SECS=420 BOUND=5 PLATEAU=50 timeout 900 nice -n 10 ./exact start_s8.sol sg176_17.txt 3 $T best_$tag.sol > log_$tag.out 2> log_$tag.err
  echo "$T $(cat log_$tag.out)" >> triples_summary.txt
done
echo done >> triples_summary.txt
