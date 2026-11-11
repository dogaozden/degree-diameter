#!/bin/bash
# Job queue for the (8,8) raise (research/squads/cells/raise-d8D8.md).
# usage: raise8_queue.sh JOBFILE OUTDIR SECS PAR
# Each JOBFILE line:  SEED ORBW GROUP-TOKENS...      (ORBW 0 = default weight)
#   e.g.  "1 0 psl 9 337"   or   "2 3 prod sl 3 sl 9 7"
# Runs haar_sym with ORBIT="3 2 2" (k=3, m=2, f=2 : Delta = 8), THREADS=1, PAR jobs at a time,
# each for SECS seconds of wall clock. Logs go to OUTDIR/<tag>.log; a cost-0 graph is written
# to OUTDIR/<tag>.txt by haar_sym (it runs its own full diameter check first).
set -u
here="$(cd "$(dirname "$0")" && pwd)"
jobs="$1"; out="$2"; secs="$3"; par="$4"
mkdir -p "$out"
while read -r seed w rest; do
  [ -z "$seed" ] && continue
  case "$seed" in \#*) continue ;; esac
  tag="d8D8_$(echo $rest | tr ' ' '_')_orb3_s${seed}"
  [ "$w" != "0" ] && tag="${tag}_ORBW${w}"
  extra=""; [ "$w" != "0" ] && extra="ORBW=$w"
  echo "cd $here/.. && env ORBIT='3 2 2' THREADS=1 $extra nice -n 5 timeout $((secs + 120)) ./haar_sym 8 8 $secs $seed 8 $out/$tag.txt $rest > $out/$tag.log 2>&1"
done < "$jobs" | xargs -d '\n' -P "$par" -I{} sh -c '{}'
echo "queue done: $jobs"
