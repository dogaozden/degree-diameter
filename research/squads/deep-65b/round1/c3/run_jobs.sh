#!/bin/bash
# usage: run_jobs.sh BUDGET_SECONDS GROUP_ID...   (runs missing chunks of sg_300_<id> with NPROC=8, resumable)
cd /home/user/degree-diameter/research/squads/deep-65b/round1/c3
BUD=$1; shift
start=$(date +%s); N=8
for g in "$@"; do
  for p in $(seq 0 $((N-1))); do
    out=out/ex_300_${g}_p${p}of${N}.txt
    if [ -f "$out" ] && grep -q TOTAL "$out"; then continue; fi
    if [ $(( $(date +%s) - start )) -ge $BUD ]; then echo "budget stop before $g p$p"; exit 0; fi
    timeout 45 nice -n 15 ./hubk tabs/sg_300_$g.txt 5 ex $N $p > "$out" 2>&1
  done
  echo "group $g: all $N chunks done"
done
