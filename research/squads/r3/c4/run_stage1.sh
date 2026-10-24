#!/bin/bash
# Round 3, card c4: knob sweep on (10,5), A4 x SL(2,3) x Z7, ORBIT="3 3 1", 120 s per run.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r3/c4
cd "$D" || exit 1
SETTINGS=(
"base 8"
"K1 1"
"K4 4"
"K16 16"
"K64 64"
"T0 8 TARGP=0"
"T50 8 TARGP=50"
"T100 8 TARGP=100"
"C5 8 COOL=5"
"C60 8 COOL=60"
"RH30 8 REHEAT=30"
"RR30 8 REHEAT=30 RESTART=1"
)
run() {  # label K seed [ENV=VAL ...]
  local label=$1 K=$2 seed=$3; shift 3
  local log="$D/log_${label}_s${seed}.log" out="$D/sol_${label}_s${seed}.txt"
  env ORBIT="3 3 1" "$@" timeout 900 nice -n 10 "$B/haar_sym" 10 5 120 "$seed" "$K" "$out" prod psl 3 sl 3 7 > "$log" 2>&1
  local best; best=$(grep '^RESULT' "$log" | sed 's/.*best=\([0-9]*\).*/\1/')
  printf '%s\tK=%s\t%s\tseed=%s\tbest=%s\n' "$label" "$K" "${*:-none}" "$seed" "$best" >> "$D/stage1.tsv"
}
declare -A ENVS
for s in "${SETTINGS[@]}"; do
  read -r -a parts <<< "$s"
  label=${parts[0]}; K=${parts[1]}; envs=("${parts[@]:2}")
  ENVS[$label]="$K|${envs[*]}"
  run "$label" "$K" 1 "${envs[@]}"
done
# seed 2 only for settings that reached <= 5 uncovered at seed 1 (preamble rule)
for s in "${SETTINGS[@]}"; do
  read -r -a parts <<< "$s"; label=${parts[0]}
  b=$(awk -F'\t' -v L="$label" '$1==L && $4=="seed=1" {sub("best=","",$5); print $5}' "$D/stage1.tsv")
  if [ -n "$b" ] && [ "$b" -le 5 ]; then
    IFS='|' read -r K envstr <<< "${ENVS[$label]}"
    read -r -a envs <<< "$envstr"
    run "$label" "$K" 2 "${envs[@]}"
  fi
done
echo done > "$D/stage1.done"
