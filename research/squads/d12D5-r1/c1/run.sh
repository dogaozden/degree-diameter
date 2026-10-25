#!/bin/bash
# usage: run.sh BASE_PATH GROUP_STEM SECS SEED   (appends one row to ceiling.txt)
C1=/home/user/degree-diameter/research/squads/d12D5-r1/c1
D=/home/user/degree-diameter/research/d12D5
base=$1; grp=$2; secs=$3; seed=$4
bname=$(basename "$base" .txt)
mkdir -p "$C1/logs"
log="$C1/logs/${bname}_${grp}_s${seed}.log"
t0=$(date +%s)
timeout 200 nice -n 10 "$D/mlift_chart" "$base" "$C1/$grp.txt" "$D/charts/fake_univ.txt" "$secs" "$seed" > "$log" 2>&1
rc=$?
t1=$(date +%s)
bc=$(grep -o 'best_cost=[0-9-]*' "$log" | head -1 | cut -d= -f2)
m=$(grep -o ' m=[0-9]*' "$log" | head -1 | cut -d= -f2)
it=$(grep -o 'iters=[0-9]*' "$log" | head -1 | cut -d= -f2)
printf "%s\t%s\tm=%s\tseed=%s\tbest_cost=%s\titers=%s\twall=%ss\trc=%s\n" "$bname" "$grp" "${m:-NA}" "$seed" "${bc:-NA}" "${it:-NA}" "$((t1-t0))" "$rc" >> "$C1/ceiling.txt"
