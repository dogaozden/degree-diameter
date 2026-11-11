#!/bin/bash
# c2-repair follow-up driver: waits for the running prod run (PID 17686), then runs the psl energy-6 states
# one at a time; no run starts after 00:30 UTC (2026-11-01).
cd /home/user/degree-diameter/research/squads/handsoff-108/c2-repair
DEADLINE=$(date -u -d "2026-11-01 00:30" +%s)
while kill -0 17686 2>/dev/null; do sleep 5; done
echo "prod_b finished (driver2) $(date -u)" >> driver.log
run() {
  local tag=$1 line=$2; shift 2
  if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "skip $tag (deadline) $(date -u)" >> driver.log; return; fi
  local S; S=$(awk -F'\t' -v L="$line" 'NR==L{print $4}' ../shared/good_states.tsv)
  echo "start $tag line $line $(date -u)" >> driver.log
  env ORBIT="3 3 1" ORBW=3 TWOMOVE=1 TWOSTATE="$S" C2K=100 C2M=1 C2SECS=1500 \
    nice -n 10 timeout 2000 ./haar_c2 10 8 1 108301 8 /dev/null "$@" > run_$tag.log 2>&1
  echo "end $tag rc=$? $(date -u)" >> driver.log
}
run e6_psl_a 8 psl 23 97
run e6_psl_b 9 psl 23 97
run e6_psl_c 10 psl 23 97
echo "driver2 done $(date -u)" >> driver.log
