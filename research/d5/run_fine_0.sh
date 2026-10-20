#!/bin/bash
# Shard-0 batch: runs the jobs in fine_0_jobs.txt, 4 at a time (all cores), each under nice.
# Launch from the repo root: scripts/guarded.sh 5 research/d5/run_fine_0.sh
cd "$(dirname "$0")" || exit 1
grep -v '^#' fine_0_jobs.txt | xargs -P 4 -L 1 nice -n 15 ./run_h4.sh
