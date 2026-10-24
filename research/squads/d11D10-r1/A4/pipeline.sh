#!/bin/bash
# A4 pipeline, run inside ONE gate slot: gate.sh 900 bash pipeline.sh
#  1. RANDORB=30 (ORBIT="3 3 2") on psl 61x661, psl 71x421, psl 127x73, one after another.
#  2. Anneal the group with the lowest RANDORB median (ORBIT="3 3 2", no ORBW, K=8, SEED=1) for 600 s, shortened
#     if the slot came late so that the anneal ends by 19:37 UTC (the card's time box is 19:45 UTC).
#  3. If solved (rc 0 and the file written), haarcheck_psl on the file.
unset THREADS
H=/home/user/degree-diameter/research/structured/haar_sym
CHK=/home/user/degree-diameter/research/structured/tools/haarcheck_psl
A=/home/user/degree-diameter/research/squads/d11D10-r1/A4
cd "$A" || exit 1
finish() { echo "$(date +%T) PIPELINE DONE"; exit 0; }
echo "$(date +%T) pipeline start (slot taken)"
: > selection.txt
for g in "61 661" "71 421" "127 73"; do
  set -- $g
  p=$1; n=$2
  echo "$(date +%T) RANDORB psl $p x Z$n"
  env ORBIT="3 3 2" RANDORB=30 timeout 150 "$H" 11 10 1 1 8 /dev/null psl "$p" "$n" > randorb_psl_${p}_${n}.log 2>&1
  echo "$(date +%T) RANDORB psl $p x Z$n rc=$?"
  line=$(grep '^RANDORB d=' randorb_psl_${p}_${n}.log)
  med=$(echo "$line" | grep -o 'median=[0-9]*' | cut -d= -f2)
  mn=$(echo "$line" | grep -o ' min=[0-9]*' | cut -d= -f2)
  mu=$(echo "$line" | grep -o 'mu=[0-9.]*' | cut -d= -f2)
  [ -n "$med" ] && echo "$p $n $mn $med $mu" >> selection.txt
  echo "$line"
done
read -r p n mn med mu < <(sort -k4,4n -k5,5g selection.txt | head -1)
[ -z "$p" ] && { echo "no RANDORB result, stop"; finish; }
left=$(( $(date -u -d "2026-10-24 19:37:00" +%s) - $(date -u +%s) ))
secs=600; [ "$left" -lt 600 ] && secs=$left
if [ "$secs" -lt 120 ]; then echo "$(date +%T) no time left for the anneal ($left s), stop"; finish; fi
OUT=$A/d11D10_psl_${p}_${n}_orb3_A4_s1.txt
echo "$(date +%T) ANNEAL psl $p x Z$n (min $mn, median $med, mu $mu) ORBIT=3 3 2 for $secs s"
env ORBIT="3 3 2" timeout $((secs + 160)) "$H" 11 10 "$secs" 1 8 "$OUT" psl "$p" "$n" > anneal_psl_${p}_${n}.log 2>&1
rc=$?
echo "$(date +%T) ANNEAL rc=$rc"
grep -E '^(RESULT|full diameter|wrote|start cost)' anneal_psl_${p}_${n}.log
if [ $rc -eq 0 ] && [ -s "$OUT" ]; then
  echo "$(date +%T) HAARCHECK $OUT"
  timeout 300 "$CHK" "$OUT" > check_psl_${p}_${n}.log 2>&1
  echo "check rc=$?"
  tail -n 2 check_psl_${p}_${n}.log
fi
finish
