#!/bin/bash
# Card k5 (own-small r2): (3,10), D=10, p=6 joint annealing (salift_s2), orders N=73..80 (n = 12N = 876..960).
# Phase 1: screen every group of orders 73..79 and 12 sampled non-abelian groups of order 80, 20 CPU s each, seed 1.
# Phase 2: restart the top 3 states (lowest cost, ties to larger N, cost > 0) from their .best files, seed 2, 80 CPU s each.
# Any cost-0 state is converted with best2edges.py and checked with score48 3 10 (lines in checks.txt).
T=/home/user/degree-diameter/research/squads/own-small/tools
G=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k5
P=6
export D=10
cd "$W" || exit 1
: > job.log; : > screen.tsv; : > checks.txt
log() { echo "$(date -u +%H:%M:%S) $*" >> "$W/job.log"; }

# cost of a run = first field of the .best header (4th field), NA if no improvement was written
cost_of() { local b="$1.best"; if [ -s "$b" ]; then head -1 "$b" | awk '{print $4}'; else echo NA; fi; }

check() { # N id seed : if a cost-0 .sol exists, convert and score it
  local f="$W/s$1_$2_$3.sol"
  if [ -s "$f" ]; then
    python3 -I "$T/best2edges.py" "$G/g$1.txt" "$f" "$f.edges" > /dev/null 2>&1
    local r; r=$("$T/bin/score48" "$f.edges" 3 10 2>&1 | tail -1)
    log "CHECK N=$1 id=$2 seed=$3 -> $r"
    echo "$1 $2 $3 $r" >> checks.txt
  fi
}

run() { # N id seed secs [START file]: one salift_s2 run, prints the cost
  local N=$1 id=$2 seed=$3 secs=$4 st=$5 out="$W/s$1_$2_$3.sol"
  rm -f "$out" "$out.best" "$out.edges"
  if [ -n "$st" ]; then
    START="$st" "$T/bin/salift_s2" $P "$G/g$N.txt" "$id" "$seed" "$secs" 10 0.3 "$out" > "$W/log_${N}_${id}_${seed}.txt" 2>&1
  else
    "$T/bin/salift_s2" $P "$G/g$N.txt" "$id" "$seed" "$secs" 10 0.3 "$out" > "$W/log_${N}_${id}_${seed}.txt" 2>&1
  fi
  cost_of "$out"
}

# Phase 1: screen
for N in 73 74 75 76 77 78 79; do
  for id in $(grep '^G ' "$G/g$N.txt" | awk '{print $3}'); do
    c=$(run $N $id 1 20)
    echo "$N $id 1 $c" >> screen.tsv; log "screen N=$N id=$id cost=$c"
    check $N $id 1
  done
done
for id in 1 3 5 7 8 11 13 15 22 28 36 49; do
  c=$(run 80 $id 1 20)
  echo "80 $id 1 $c" >> screen.tsv; log "screen N=80 id=$id cost=$c"
  check 80 $id 1
done

# Phase 2: push the top 3 (cost > 0, lowest cost, ties to larger N) with START restarts and a new seed
top=$(awk '$4 ~ /^[0-9]+$/ && $4 > 0 {print $4, -$1, $2}' screen.tsv | sort -n -k1,1 -k2,2 | head -3)
echo "$top" > push_list.txt; log "push list: $(echo $top)"
echo "$top" | while read c mN id; do
  N=$((-mN))
  st="$W/s${N}_${id}_1.sol.best"
  [ -s "$st" ] || { log "no start state for N=$N id=$id"; continue; }
  c2=$(run $N $id 2 80 "$st" < /dev/null)
  echo "$N $id 2 $c2 (START cost $c)" >> screen.tsv; log "push N=$N id=$id from cost $c -> $c2"
  check $N $id 2
done

# Summary: best state overall (for the report)
best=$(awk '$4 ~ /^[0-9]+$/ {print $4, $1, $2, $3}' screen.tsv | sort -n -k1,1 -k2,2 -k3,3 | head -1)
log "best overall (cost N id seed): $best"
