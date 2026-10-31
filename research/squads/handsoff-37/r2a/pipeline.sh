#!/bin/bash
# For every far-0 168 seed: exhaustive insertion k=2 (pair + ab) then k=3 (three edges); summary to logs/pipeline.txt
cd /home/user/degree-diameter/research/squads/handsoff-37/r2a
for f in seeds/*.edges; do
  case "$f" in *cal_*) continue;; esac
  r=$(./score37 "$f"); echo "$r" | grep -q 'far=0 diam=7' || { echo "skip $f: $r" >> logs/pipeline.txt; continue; }
  b=$(basename "$f" .edges)
  for K in 2 3; do
    out=out/ins/${b}_k${K}
    timeout 500 nice -n 10 ./insert "$f" $K 0 5 "$out" > logs/ins_${b}_k${K}.txt 2> logs/ins_${b}_k${K}.err
    echo "$b k=$K $(grep -o 'best_far=[0-9]*' logs/ins_${b}_k${K}.txt) $(grep 'top far' logs/ins_${b}_k${K}.txt)" >> logs/pipeline.txt
  done
done
echo PIPELINE_DONE >> logs/pipeline.txt
