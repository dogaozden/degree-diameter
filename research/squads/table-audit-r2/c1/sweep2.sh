#!/bin/bash
# batch 2: focus on the closest splits, 75 s each, longer cooling cycle
cd /home/user/degree-diameter/research/squads/table-audit-r2/c1
for spec in "10 80 2 1.5" "10 80 3 6.0" "12 67 2 1.5"; do
  set -- $spec
  out=/home/user/degree-diameter/research/squads/table-audit-r2/c1/g_${1}_${2}_s${3}_T$4.txt
  res=$(timeout 900 nice -n 10 ../bin/sym_anneal $1 $2 10 75 $3 "$out" $4 0.1 200000 2>/dev/null)
  echo "$1 $2 T0=$4 seed=$3 :: $res"
done
