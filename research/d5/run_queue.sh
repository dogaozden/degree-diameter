#!/bin/bash
# Shard-0 queue: runs the jobs in fine_0_all.txt that have no finished log (no best= line), 4 at a time.
# Safe to re-run after a stop: finished jobs are skipped. Launch from the repo root: scripts/guarded.sh 5 research/d5/run_queue.sh
cd "$(dirname "$0")" || exit 1
while read -r d t seed secs k; do
  case "$d" in ''|\#*) continue ;; esac
  tag="d${d}_${t}_s${seed}_K${k}"
  grep -q 'best=' "logs/h4_$tag.log" 2>/dev/null && continue
  echo "$d $t $seed $secs $k"
done < fine_0_all.txt | xargs -P 4 -L 1 nice -n 15 ./run_h4.sh
