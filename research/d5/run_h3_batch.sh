#!/bin/bash
# Runs every job line "d table secs" of h3_jobs.txt through run_h3.sh: at most MAX at once, each under nice -n 10.
# Launch (from the repo root, under the autopilot time limit and stop switch):
#   nohup scripts/guarded.sh 8 research/d5/run_h3_batch.sh > research/d5/logs/h3_batch.log 2>&1 &
# JOBS overrides the job file (for tests). A TERM (from guarded.sh) is passed on to the running jobs.
cd /Users/dogaozden/AI_Projects/degree-diameter/research/d5 || exit 1
JOBS=${JOBS:-h3_jobs.txt}
MAX=${MAX:-6}
pids=()
trap 'kill -TERM "${pids[@]}" 2>/dev/null; exit 143' TERM INT
while read -r d table secs; do
  case "$d" in ""|\#*) continue ;; esac
  while [ "$(jobs -rp | wc -l)" -ge "$MAX" ]; do sleep 5; done
  echo "$(date '+%F %T') start d=$d table=$table secs=$secs"
  nice -n 10 ./run_h3.sh "$d" "$table" "$secs" &
  pids+=($!)
done < "$JOBS"
wait
echo "$(date '+%F %T') all jobs finished"
