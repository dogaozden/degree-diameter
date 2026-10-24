#!/bin/bash
# c1 calibration: ORBIT="3 5 1", d=16 D=8, SL(2,p) x Z_n with mu ~ 9.4, 13.9, 18.2, 21.9, 25.0, 29.9.
# Two lanes (seed 1 and seed 2), one run at a time per lane, each run THREADS=1, nice 10, budget 240 s.
T=/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured
C1=/home/user/degree-diameter/research/squads/d16D10-r1/c1
mkdir -p "$C1/logs"
GRPS="43:163 41:193 53:91 37:271 61:61 37:277"
SUM="$C1/logs/summary.txt"
lane() {
  seed=$1
  for g in $GRPS; do
    p=${g%%:*}; n=${g##*:}
    tag=sl${p}x${n}
    t0=$(date +%s)
    ORBIT="3 5 1" THREADS=1 timeout 290 nice -n 10 "$T/haar_sym" 16 8 240 "$seed" 8 "$C1/logs/sol_${tag}_s${seed}.txt" sl "$p" "$n" \
      > "$C1/logs/${tag}_s${seed}.out" 2> "$C1/logs/${tag}_s${seed}.err"
    rc=$?
    echo "$tag seed=$seed rc=$rc wall=$(( $(date +%s) - t0 ))s $(cat "$C1/logs/${tag}_s${seed}.out") | load=$(cut -d' ' -f1 /proc/loadavg)" >> "$SUM"
  done
}
rm -f "$SUM"
echo "start $(date +%T) load=$(cut -d' ' -f1 /proc/loadavg)" >> "$SUM"
lane 1 &
lane 2 &
wait
echo "ALLDONE $(date +%T)" >> "$SUM"
