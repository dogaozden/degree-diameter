#!/bin/bash
# batch 2: remaining K=3 triples in order of 1-change cost (time-boxed), started after batch 1 finishes
cd /home/user/degree-diameter/research/squads/s384r2/c4
until grep -q done triples_summary.txt 2>/dev/null; do sleep 5; done
start=$(date +%s)
while read T; do
  now=$(date +%s); if [ $((now-start)) -gt 840 ]; then echo "time box reached" >> triples_summary2.txt; break; fi
  tag=$(echo $T | tr , _)
  PLAT=plat_$tag.txt SECS=120 BOUND=5 PLATEAU=50 timeout 300 nice -n 10 ./exact start_s8.sol sg176_17.txt 3 $T best_$tag.sol > log_$tag.out 2> log_$tag.err
  echo "$T $(cat log_$tag.out)" >> triples_summary2.txt
done < batch2_list.txt
echo done2 >> triples_summary2.txt
