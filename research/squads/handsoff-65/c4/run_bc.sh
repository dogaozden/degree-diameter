#!/bin/bash
# usage: run_bc.sh H DELTA ORDER ID...   exhaustive bi-coset search B(G;H,K), |H|=H_ORDER, all class pairs (H,K),
# all unions of double cosets with total degree DELTA (dcenum, D=5). One line per (group, pair) in c4/results.txt.
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
C4=/home/user/degree-diameter/research/squads/handsoff-65/c4
H=$1; DELTA=$2; ORDER=$3; shift 3
for ID in "$@"; do
  dir=$C4/tmp/h${H}_g${ORDER}_${ID}; mkdir -p $dir
  gap -q -c "Read(\"$SH/dc2_lib.g\"); G:=SmallGroup($ORDER,$ID); ExportPairs(G, $H, \"$dir/p\"); QUIT;" > $dir/gap.log 2>&1
  for f in $dir/p_*.dc2; do
    [ -e "$f" ] || continue
    r=$(timeout 600 nice -n 10 $SH/dcenum $f $DELTA 5 $dir/$(basename ${f%.dc2})_best.edges 2>/dev/null | tail -1)
    echo "h$H d$DELTA $ORDER $ID $(basename ${f%.dc2}) | $(echo "$r" | sed 's/set.*//')" >> $C4/results_h${H}_d${DELTA}.txt
    case "$r" in *"best 0 "*) echo "HIT $ORDER $ID $f" >> $C4/HITS.txt;; esac
  done
  case "$(ls $dir)" in *"gap.log"*) ;; esac
done
