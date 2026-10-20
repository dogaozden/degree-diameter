#!/usr/bin/env bash
# run_batch.sh JOBFILE P : run each line "D d G0 c seed seconds K" of JOBFILE with P parallel workers (run_job.sh).
cd "$(dirname "$0")"
grep -v '^#' "$1" | grep -v '^\s*$' | xargs -P "$2" -L 1 ./run_job.sh
