#!/bin/bash
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/b4
T=../../tools
export OMP_NUM_THREADS=1 THREADS=1
for spec in "204 7" "204 8" "208 6" "208 8" "208 25" "208 46" "210 2" "210 8"; do
  set -- $spec
  [ -s g$1_$2.bin ] || timeout 200 nice -n 10 python3 $T/gapgroup.py table $1 $2 g$1_$2.bin >> gap.log 2>&1
  echo "GAP $1 $2 rc=$? $(date +%T)"
done
run() { # file
  while read tag spec base; do
    [ -z "$tag" ] && continue
    s=$(echo $RANDOM); o=out/${tag}_${base%.txt}_$(echo $spec | tr ':' '_').sol
    res=$(timeout 30 nice -n 10 $T/flift $base $spec 7 5 6 $s 8 $o 2>&1 | grep RESULT)
    echo "$tag $spec $base :: $res $(date +%T)"
  done < $1
}
run jobs_A.txt
run jobs_B.txt
run jobs_C.txt
echo ALLDONE $(date +%T)
