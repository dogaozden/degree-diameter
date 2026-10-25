#!/bin/bash
# Squad c4 sweep (orders 157..170 except 160). Jobs in jobs1.txt order (metacyclic N=3..10, then cyclic, then Z_a x Z_b).
# Stage 1: SEED=1, 60 s per job. Cost 1..2 -> stage 2: SEED=2, 150 s. Cost 0 -> lift + apsp check at once.
# One heavy process at a time (PAR=1), everything serial.
C=/home/user/degree-diameter/research/squads/r3-chartlift/c4
CH=/home/user/degree-diameter/research/theorems/chartlift
CHART=$CH/r3/k5q3_pd_star23.txt
FLAGS=$CH/r3/k5q3_pd_star23.flags
export BIN=$C/ctrl_search
cd "$CH" || exit 1

cost_of() { grep -o 'best_cost=[0-9]*' "$1" 2>/dev/null | head -n 1 | cut -d= -f2; }

verify() {   # $1 = .ctrl file, $2 = label
  timeout 900 nice -n 10 python3 lift.py "$1" "$CHART" 3 5 "$C/x_$2.edges" > "$C/ver_$2.log" 2>&1
  timeout 900 nice -n 10 "$C/apsp" "$C/x_$2.edges" 15 5 >> "$C/ver_$2.log" 2>&1
  timeout 900 nice -n 10 "$C/apsp" "$C/x_$2.edges" 15 4 >> "$C/ver_$2.log" 2>&1
  rm -f "$C/x_$2.edges"
  echo "$2 $(grep -h 'RESULT\|diameter=\|^controller' "$C/ver_$2.log" | tr '\n' ' ')" >> "$C/verify.log"
}

while read -r b g t <&3; do
  if [ ! -f "$g" ]; then echo "missing group file $g" >> "$C/progress.log"; continue; fi
  echo "$b $g $t" > "$C/job_s1.txt"
  PAR=1 SEED=1 bash "$CH/r3/batch.sh" "$C/job_s1.txt" "$FLAGS" 60 "$C/runs1" >> "$C/progress.log" 2>&1
  c=$(cost_of "$C/runs1/$t.out")
  echo "S1 $t cost=$c $(date +%T)" >> "$C/progress.log"
  if [ "$c" = "0" ]; then verify "$C/runs1/$t.ctrl" "s1_$t"; fi
  if [ -n "$c" ] && [ "$c" -ge 1 ] && [ "$c" -le 2 ]; then
    echo "$b $g $t" > "$C/job_s2.txt"
    PAR=1 SEED=2 bash "$CH/r3/batch.sh" "$C/job_s2.txt" "$FLAGS" 150 "$C/runs2" >> "$C/progress.log" 2>&1
    c2=$(cost_of "$C/runs2/$t.out")
    echo "S2 $t cost=$c2 $(date +%T)" >> "$C/progress.log"
    if [ "$c2" = "0" ]; then verify "$C/runs2/$t.ctrl" "s2_$t"; fi
  fi
done 3< "$C/jobs1.txt"
echo "SWEEP DONE $(date +%T)" >> "$C/progress.log"
