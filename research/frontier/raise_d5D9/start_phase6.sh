#!/bin/bash
cd "$(dirname "$0")"
while [ "$(wc -l < phase5.log)" -lt 48 ]; do sleep 10; done
SECS=150 K=8 xargs -P4 -I{} ./run_job.sh {} < phase6_jobs.txt > phase6.log 2>&1
