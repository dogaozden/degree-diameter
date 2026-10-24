#!/bin/bash
# B5 speed driver, run through gate.sh with SECS 240. Sequential, single-thread haar_sym runs in ORBIT mode.
# Every run: VCLOCK=0.01 MAXSTEPS=10 (K=8, so 81 evaluations), TRACE=1, seed 1, same S trajectory for all settings.
# Time per evaluation is taken from the RESULT line (time from the start of the annealing loop, setup excluded).
unset THREADS
export OMP_NUM_THREADS=1
B=/home/user/degree-diameter/research/squads/d11D10-r1/B5
H=/home/user/degree-diameter/research/structured/haar_sym
MAXSTEPS=10
LIMIT=${LIMIT:-150}      # no new run starts after this many seconds of driver time
HARD=200                 # every run is cut off at HARD seconds of driver time (gate timeout is 240)
SUM=$B/speed_summary.tsv
mkdir -p "$B/logs"
START=$(date +%s.%N)
printf 'run\tgroup\tfast\thwmin\thwmax\tpfd\tsetup_s\twide\tevals\ttime_s\tus_per_eval\tevals_per_s\thash\tbest\tload1\tstatus\n' > "$SUM"

run() {  # run NAME GROUP ORBIT ORBW FAST HWMIN HWMAX PFD
  local name=$1 grp=$2 orbit=$3 orbw=$4 fast=$5 hwmin=$6 hwmax=$7 pfd=$8
  local el load tl gargs log out rc envs setup wide hash res best evals tm us rate status
  el=$(awk -v a="$START" -v b="$(date +%s.%N)" 'BEGIN{printf "%.1f", b-a}')
  load=$(cut -d' ' -f1 /proc/loadavg)
  if awk -v e="$el" -v l="$LIMIT" 'BEGIN{exit !(e > l)}'; then
    printf '%s\t%s\t%s\t%s\t%s\t%s\t-\t-\t-\t-\t-\t-\t-\t-\t%s\tSKIPPED at driver t=%s\n' \
      "$name" "$grp" "$fast" "$hwmin" "$hwmax" "$pfd" "$load" "$el" >> "$SUM"
    return
  fi
  tl=$(awk -v e="$el" -v h="$HARD" 'BEGIN{t=h-e; if (t > 90) t = 90; printf "%d", t}')
  if [ "$grp" = psl ]; then gargs="psl 101 151"; else gargs="sl 79 151"; fi
  log=$B/logs/$name.log; out=$B/out_$name.txt
  envs=(ORBIT="$orbit" TRACE=1 VCLOCK=0.01 MAXSTEPS=$MAXSTEPS FAST=$fast HWMIN=$hwmin HWMAX=$hwmax PFD=$pfd)
  if [ -n "$orbw" ]; then envs+=(ORBW="$orbw"); fi
  timeout "$tl" env "${envs[@]}" "$H" 11 10 1000 1 8 "$out" $gargs > "$log" 2>&1
  rc=$?
  setup=$(sed -n 's/.*setup \([0-9.]*\)s.*/\1/p' "$log" | head -n 1)
  wide=$(grep -m 1 'wide rows' "$log" | tr -d ',;\t' | cut -c1-80)
  [ -z "$wide" ] && wide=none
  hash=$(sed -n 's/^TRACE steps=[0-9]* hash=\([0-9a-f]*\).*/\1/p' "$log" | head -n 1)
  res=$(grep -m 1 '^RESULT' "$log" | sed -n 's/.*best=\([-0-9]*\) evals=\([0-9]*\) time=\([0-9.]*\).*/\1 \2 \3/p')
  if [ -n "$res" ] && [ -n "$hash" ]; then
    set -- $res
    best=$1; evals=$2; tm=$3
    us=$(awk -v t="$tm" -v e="$evals" 'BEGIN{ if (t > 0) printf "%.0f", 1e6 * t / e; else print "-" }')
    rate=$(awk -v t="$tm" -v e="$evals" 'BEGIN{ if (t > 0) printf "%.3f", e / t; else print "-" }')
    status=ok
  else
    best=-; evals=-; tm=-; us=-; rate=-; hash=-; status="FAILED_rc=$rc"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "$grp" "$fast" "$hwmin" "$hwmax" "$pfd" "${setup:--}" "$wide" "$evals" "$tm" "$us" "$rate" "$hash" "$best" "$load" "$status" >> "$SUM"
}

# essentials first: FAST=1 and default (FAST=2, HWMIN 64, HWMAX 256, PFD 8) on both groups
run psl_f1     psl "5 2 1" 5  1 64 256 8
run psl_def    psl "5 2 1" 5  2 64 256 8
run sl_f1      sl  "3 3 2" "" 1 64 256 8
run sl_def     sl  "3 3 2" "" 2 64 256 8
# prefetch distance
run psl_pfd0   psl "5 2 1" 5  2 64 256 0
run sl_pfd0    sl  "3 3 2" "" 2 64 256 0
run psl_pfd16  psl "5 2 1" 5  2 64 256 16
run sl_pfd16   sl  "3 3 2" "" 2 64 256 16
# subgroup order range
run psl_hwmax128 psl "5 2 1" 5  2 64 128 8
run sl_hwmax128  sl  "3 3 2" "" 2 64 128 8
run psl_hw32_64  psl "5 2 1" 5  2 32 64 8
run sl_hw32_64   sl  "3 3 2" "" 2 32 64 8
# drift check: the default again, last
run psl_def2   psl "5 2 1" 5  2 64 256 8
run sl_def2    sl  "3 3 2" "" 2 64 256 8

echo "DRIVER DONE t=$(awk -v a="$START" -v b="$(date +%s.%N)" 'BEGIN{printf "%.1f", b-a}')"
