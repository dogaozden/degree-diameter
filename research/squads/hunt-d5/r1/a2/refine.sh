#!/bin/bash
# refine top 5 groups: extra plain seeds, then orbit search with order-2/3/4 automorphisms
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a2
H=/home/user/degree-diameter/research/squads/hunt-d5/tools
for g in "210 2" "216 161" "216 33" "216 88" "216 26"; do
  set -- $g; N=$1; I=$2; T=tab/g${N}_${I}.bin
  for K in 2 3 4; do
    timeout 200 nice -n 10 python3 $H/gapgroup.py table $N $I $T $K >/dev/null 2>&1
  done
  for SEED in 2 3 4; do
    R=$(OMP_NUM_THREADS=1 timeout 60 nice -n 10 $H/haar5 anneal $T 5 6 $SEED 2>&1 | grep RESULT)
    echo "$N $I plain seed=$SEED :: $R" >> refine_out.txt
  done
  for K in 2 3 4; do
    AF=$T.aut$K; [ -f $AF ] || continue
    NL=$(wc -l < $AF)
    for AL in 0 1; do
      [ $AL -lt $NL ] || continue
      case $K in
        2) ORB="2 2 1" ;;
        3) ORB="3 1 2" ;;
        4) ORB="4 1 1" ;;
      esac
      R=$(AUT=$AF ALINE=$AL ORBIT="$ORB" OMP_NUM_THREADS=1 timeout 60 nice -n 10 $H/haar5 anneal $T 5 6 1 2>&1 | grep RESULT)
      echo "$N $I aut$K line=$AL orbit=\"$ORB\" :: $R" >> refine_out.txt
    done
  done
done
echo DONE >> refine_out.txt
