#!/bin/sh
# run_jobs.sh JOBFILE OUTFILE SECONDS : run_one.sh on each job line, 4 at a time.
cd "$(dirname "$0")"
xargs -P 4 -L 1 ./run_one.sh "$3" < "$1" >> "$2" 2>&1
echo "BATCH DONE $1" >> "$2"
