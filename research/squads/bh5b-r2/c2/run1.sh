#!/bin/bash
# card c2: export the |H|=3 bi-coset files for the three near-miss groups, then one fast anneal per group (SECS of CPU time).
cd /home/user/degree-diameter/research/squads/bh5b-r2/c2
mkdir -p dc logs
for spec in "1806 15" "1806 2" "1830 2"; do set -- $spec
  timeout 300 nice -n 10 gap -q -c "ORDER:=$1; H_ORDER:=3; OUTDIR:=\"dc\"; IDS:=[$2];" sg_export.g > /dev/null 2>&1
done
for f in dc/sg1806_15_1_1.dc2 dc/sg1806_2_1_1.dc2 dc/sg1830_2_1_1.dc2; do
  b=$(basename ${f%.dc2})
  start=$(date +%s)
  r=$(SA=1 SECS=60 SEED=1 ITERS=100000 timeout 1500 nice -n 10 ./dcenum $f 7 5 logs/${b}_best.edges 2>/dev/null | tail -1)
  echo "$b wall $(( $(date +%s) - start ))s :: $r" >> logs/c2_run1.txt
  case "$r" in *"best 0 "*) cp logs/${b}_best.edges logs/HIT_${b}.edges;; esac
done
echo DONE >> logs/c2_run1.txt
