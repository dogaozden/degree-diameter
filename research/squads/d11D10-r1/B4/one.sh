#!/bin/bash
# B4 one.sh ORBIT FAM P N LOG: one RANDORB=3 LEVELS=3 screen (SECONDS=1, SEED=1, K=8, OUTFILE /dev/null), run inside the gate.
# Appends the time spent inside the gate (setup + screen) to LOG, so the heavy budget can be counted.
H=/home/user/degree-diameter/research/structured/haar_sym
t0=$(date +%s.%N)
env -u THREADS ORBIT="$1" RANDORB=3 LEVELS=3 "$H" 11 10 1 1 8 /dev/null "$2" "$3" "$4" > "$5" 2>&1
rc=$?
t1=$(date +%s.%N)
echo "B4_INSIDE_SECONDS $(awk "BEGIN{printf \"%.2f\", $t1-$t0}") rc=$rc" >> "$5"
exit $rc
