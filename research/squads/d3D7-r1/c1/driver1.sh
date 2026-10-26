#!/bin/bash
# Step 1 breadth: 1 seed x 60 s per (group, p), one run at a time.
cd /home/user/degree-diameter
OUT=research/squads/d3D7-r1/c1
: > $OUT/runs.tsv
run() { # N p id name seed secs [T0 T1]
  local N=$1 p=$2 id=$3 name=$4 seed=$5 secs=$6 t0=${7:-10} t1=${8:-0.3}
  local sol=$OUT/sol_${N}_${id}_${seed}_p${p}.sol
  local log=$OUT/log_${N}_${id}_p${p}_s${seed}_T${t0}.txt
  timeout 900 nice -n 10 research/d3D7/bin/salift $p research/d3D7/groups/g$N.txt $id $seed $secs $t0 $t1 $sol > $log 2>&1
  local line=$(grep '^end best' $log | tail -1)
  local best=$(echo "$line" | awk '{print $3}'); local its=$(echo "$line" | awk '{print $5}')
  local found=""; grep -q FOUND $log && found=FOUND
  printf "%s\t%s\t%s\t%s\t%d\t%d\t%s\t%s\t%s\tT0=%s\t%s\n" "$N" "$id" "$name" "$p" $((2*p*N)) "$seed" "$best" "$its" "$secs" "$t0" "$found" >> $OUT/runs.tsv
}
# smallest n first: n = 2pN
# (N=11,p=8,n=176) (N=12,p=8,n=192) (N=13,p=7,n=182) (N=14,p=7,n=196) (N=15,p=6,n=180) (N=16,p=6,n=192)
# n=176: N=11 p=8
run 11 8 1 C11 1 60
# n=180: N=15 p=6
run 15 6 1 C15 1 60
# n=182: N=13 p=7
run 13 7 1 C13 1 60
# n=192: N=12 p=8 (5 groups)
for id in 1 2 3 4 5; do name=$(grep "^G 12 $id " research/d3D7/groups/g12.txt | awk '{print $4}'); run 12 8 $id $name 1 60; done
# n=192: N=16 p=6 (14 groups)
for id in $(seq 1 14); do name=$(grep "^G 16 $id " research/d3D7/groups/g16.txt | awk '{print $4}'); run 16 6 $id $name 1 60; done
# n=196: N=14 p=7 (2 groups)
for id in 1 2; do name=$(grep "^G 14 $id " research/d3D7/groups/g14.txt | awk '{print $4}'); run 14 7 $id $name 1 60; done
echo DONE > $OUT/step1.done
