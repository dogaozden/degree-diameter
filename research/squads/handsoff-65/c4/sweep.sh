#!/bin/bash
# usage: sweep.sh MODE H DELTA SECS ORDER ID...   MODE ex = exhaustive dcenum, sa = annealing (SECS per pair).
# Bi-coset graphs B(G;H,K), |H| = H, all class pairs (H,K) of core-free subgroups of order H (dc2_export via dc2_lib.g).
# One line per (group, pair) in c4/results.txt. A cost-0 graph is copied to c4/HITS/.
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
C4=/home/user/degree-diameter/research/squads/handsoff-65/c4
MODE=$1; H=$2; DELTA=$3; SECS=$4; ORDER=$5; shift 5
mkdir -p $C4/HITS
for ID in "$@"; do
  dir=$C4/tmp/${MODE}_h${H}_g${ORDER}_${ID}; mkdir -p $dir
  gap -q -c "Read(\"$SH/dc2_lib.g\"); G:=SmallGroup($ORDER,$ID); ExportPairs(G, $H, \"$dir/p\"); QUIT;" > $dir/gap.log 2>&1
  npairs=0
  for f in $dir/p_*.dc2; do
    [ -e "$f" ] || continue
    npairs=$((npairs+1)); b=$(basename ${f%.dc2})
    if [ "$MODE" = ex ]; then
      r=$(timeout 300 nice -n 10 $SH/dcenum $f $DELTA 5 $dir/$b.edges 2>/dev/null | tail -1)
    else
      r=$(SA=1 SECS=$SECS SEED=1 timeout $((SECS*3+60)) nice -n 10 $SH/dcenum $f $DELTA 5 $dir/$b.edges 2>/dev/null | tail -1)
    fi
    echo "$MODE h$H d$DELTA $ORDER $ID $b | $(echo "$r" | sed 's/set.*//' | sed 's/^RESULT //')" >> $C4/results.txt
    case "$r" in *"best 0 "*) cp $dir/$b.edges $C4/HITS/g${ORDER}_${ID}_${b}.edges; echo "HIT $ORDER $ID $b" >> $C4/HITS.txt;; esac
  done
  [ $npairs -eq 0 ] && echo "$MODE h$H $ORDER $ID NOPAIRS" >> $C4/results.txt
  rm -rf $dir
done
