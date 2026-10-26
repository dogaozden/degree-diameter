#!/bin/bash
# batch 1: one seed per split, T0=3.0, T1=0.1, cycle 100000 iters, 45 s each
cd /home/user/degree-diameter/research/squads/table-audit-r2/c1
for bc in "4 200" "4 202" "6 135" "8 100" "10 80" "12 67" "16 50" "20 40" "32 25" "40 20"; do
  set -- $bc
  out=/home/user/degree-diameter/research/squads/table-audit-r2/c1/g_${1}_${2}_s1_T3.txt
  res=$(timeout 900 nice -n 10 ../bin/sym_anneal $1 $2 10 45 1 "$out" 3.0 0.1 100000 2>/dev/null)
  echo "$1 $2 T0=3.0 seed=1 :: $res"
done
