#!/bin/bash
# c2-repair driver: sequential exact two-move runs, one heavy process at a time (nice 10, timeout per run).
cd /home/user/degree-diameter/research/squads/handsoff-108/c2-repair
DEADLINE=$(date -u -d "2026-11-01 00:40" +%s)
run() {   # run TAG LINE GROUP-ARGS...   (LINE = data line of shared/good_states.tsv, 1-based incl. header)
  local tag=$1 line=$2; shift 2
  if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "skip $tag (deadline) $(date -u)" >> driver.log; return; fi
  local S; S=$(awk -F'\t' -v L="$line" 'NR==L{print $4}' ../shared/good_states.tsv)
  echo "start $tag line $line $(date -u)" >> driver.log
  env ORBIT="3 3 1" ORBW=3 TWOMOVE=1 TWOSTATE="$S" C2K=100 C2M=1 C2SECS=1500 \
    nice -n 10 timeout 2000 ./haar_c2 10 8 1 108301 8 /dev/null "$@" > run_$tag.log 2>&1
  echo "end $tag rc=$? $(date -u)" >> driver.log
}
run e3_psl_a 2 psl 23 97
run e3_psl_b 3 psl 23 97
run e6_prod_a 4 prod psl 7 sl 8 7 7
run e6_prod_b 5 prod psl 7 sl 8 7 7
run e6_psl_a 8 psl 23 97
run e6_psl_b 9 psl 23 97
run e6_psl_c 10 psl 23 97
run e6_prod_c 6 prod psl 7 sl 8 7 7
run e6_prod_d 7 prod psl 7 sl 8 7 7
run e6_psl_d 11 psl 23 97
run e6_psl_e 12 psl 23 97
run e6_psl_f 13 psl 23 97
echo "driver done $(date -u)" >> driver.log
