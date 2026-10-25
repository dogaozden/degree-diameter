#!/bin/bash
# Head-to-head of search variants on the same groups, seeds and wall-clock budget.
# usage: cmp.sh SECS "SEEDS" [PAR] < list      (default SEEDS "1 2 3 4", PAR = 4 parallel single-thread runs)
# list lines:  VARIANT | d D GROUP... n
#   VARIANT = random            random-S annealing (haar_fast)
#           = k m f [VAR=x ...] orbit annealing (haar_sym, ORBIT="k m f", extra environment variables)
# e.g.  random | 9 8 sl 27 13          3 2 3 | 9 8 sl 27 13          3 3 0 | 9 8 sl 27 13
# Output lines "<variant> d D grp seed s :: RESULT ...", one per run, for cmp_table.py.
# SAVE=dir: keep each run's solution and log as dir/<tag>.txt, dir/<tag>.log (orbq.sh names; random runs get "rnd"
# for the orbit tag) and append build_haar2.py's verdict to the log of every solution (N <= 10M), as orbq.sh does.
SECS=$1; SEEDS=${2:-1 2 3 4}; PAR=${3:-4}
HERE=$(cd "$(dirname "$0")" && pwd); HF=$HERE/../haar_fast; HS=$HERE/../haar_sym
run() {   # VARIANT_LABEL SEED d D grp...
  lab=$1; s=$2; shift 2; d=$1; D=$2; shift 2; grp="$*"; sol=/dev/null; log=$(mktemp)
  if [ -n "$SAVE" ]; then
    if [ "$lab" = random ]; then o=rnd; else o="orb${lab%%,*}"; [ "$lab" != "${lab%,0}" ] && o="${o}f0"; fi
    tag="d${d}D${D}_${grp// /_}_${o}_s${s}"; sol=$SAVE/$tag.txt; log=$SAVE/$tag.log; fi
  if [ "$lab" = random ]; then timeout $((SECS + 30)) "$HF" $d $D $SECS $s 8 $sol $grp > $log.tmp 2>&1
  else read -r k m f env <<< "${lab//,/ }"
       env ORBIT="$k $m $f" $env timeout $((SECS + 30)) "$HS" $d $D $SECS $s 8 $sol $grp > $log.tmp 2>&1; fi
  r=$(grep RESULT $log.tmp)
  if [ -n "$SAVE" ]; then mv $log.tmp $log
    if [ -s "$sol" ] && [ "$(head -1 $sol | awk '{print $NF}')" -le 10000000 ]; then python3 "$CHECK" "$sol" 2>&1 | tail -3 >> "$log"; fi
  else rm -f $log.tmp $log; fi
  echo "$lab $d $D $grp seed $s :: $r"
}
CHECK=$HERE/../../frontier/build_haar2.py
export -f run; export SECS HF HS SAVE CHECK
while IFS= read -r line; do
  [[ -z "$line" || "$line" =~ ^# ]] && continue
  v=$(echo "${line%%|*}" | xargs); rest=$(echo "${line#*|}" | xargs)
  for s in $SEEDS; do echo "${v// /,} $s $rest"; done
done | xargs -P "$PAR" -L 1 bash -c 'run "$@"' _
