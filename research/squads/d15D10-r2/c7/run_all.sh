#!/bin/bash
# c7: (15,8) psl 19 x Z2651 proxy, ORBIT="5 3 0", annealing-settings sweep, 2 seeds per setting, 100 s per run.
# Runs one at a time through a light slot (slot.sh). Raw output in raw/, one summary line per run in results.txt.
C7=/home/user/degree-diameter/research/squads/d15D10-r2/c7
SL=/home/user/degree-diameter/research/squads/d15D10-r2/slot.sh
cd /home/user/degree-diameter/research/lowmem || exit 1
: > "$C7/results.txt"
run() {   # name K envs seed
  local name=$1 K=$2 envs=$3 seed=$4
  local raw="$C7/raw/${name}_s${seed}.txt"
  $SL timeout 110 nice -n 10 env ORBIT="5 3 0" $envs ./haar_lean 15 8 100 "$seed" "$K" /dev/null psl 19 2651 > "$raw" 2>&1
  local rc=$?
  local res; res=$(grep '^RESULT' "$raw")
  if [ -z "$res" ]; then
    printf '%s\tK=%s\t%s\tseed=%s\tNO RESULT (rc=%s)\n' "$name" "$K" "$envs" "$seed" "$rc" >> "$C7/results.txt"; return
  fi
  local best evals t solved=no
  best=$(echo "$res" | grep -o ' best=[^ ]*' | cut -d= -f2)
  evals=$(echo "$res" | grep -o ' evals=[^ ]*' | cut -d= -f2)
  t=$(echo "$res" | grep -o ' time=[^ ]*' | cut -d= -f2)
  [ "$best" = 0 ] && solved=yes
  printf '%s\tK=%s\t%s\tseed=%s\tsolved=%s\tevals=%s\tbest=%s\ttime=%s\n' "$name" "$K" "$envs" "$seed" "$solved" "$evals" "$best" "$t" >> "$C7/results.txt"
}
for seed in 1 2; do run base 8 "TARGP=70 ORBW=1" "$seed"; done
for seed in 1 2; do run K4 4 "TARGP=70 ORBW=1" "$seed"; done
for seed in 1 2; do run K16 16 "TARGP=70 ORBW=1" "$seed"; done
for seed in 1 2; do run T40 8 "TARGP=40 ORBW=1" "$seed"; done
for seed in 1 2; do run T95 8 "TARGP=95 ORBW=1" "$seed"; done
for seed in 1 2; do run W5 8 "TARGP=70 ORBW=5" "$seed"; done
for seed in 1 2; do run TM03 8 "TARGP=70 ORBW=1 TMIN=0.3" "$seed"; done
echo "DONE $(date +%s)" >> "$C7/results.txt"
touch "$C7/DONE"
