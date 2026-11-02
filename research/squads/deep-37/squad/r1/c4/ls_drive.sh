#!/bin/bash
# ls_drive.sh SECS GROUPDIR... : colour-preserving families only (est.txt lines with desc "A:"), up to 3 SAT-feasible per
# group; mkstart.py start graph, symbo breakout for SECS seconds; the result is kept only if it is a valid cubic bipartite graph.
cd /home/user/degree-diameter/research/squads/deep-37
T=$1; shift
for g in "$@"; do
  k=0
  while read f e desc; do
    [ $k -ge 3 ] && break
    case "$desc" in A:*) ;; *) continue;; esac
    b=$(basename $(dirname $f))_$(basename $f .txt)
    st=squad/r1/c4/st/$b.edges
    r=$(timeout 30 nice -n 15 python3 squad/r1/c4/mkstart.py $f $st 1 2>&1 | tail -1)
    case "$r" in UNSAT*) continue;; esac
    [ -f $st ] || continue
    k=$((k+1))
    out=squad/r1/c4/ls/$b
    timeout 100 nice -n 15 squad/r1/c4/symbo $f $st $T 1 $out > $out.log 2>&1
    if [ -f ${out}_best.edges ]; then
      chk=$(bin/score37 ${out}_best.edges 2>&1 | tail -1)
      case "$chk" in *"maxdeg=3 simple=yes bipartite=yes"*) ok=valid;; *) ok=INVALID;; esac
      best=$(echo "$chk" | sed 's/.*far=\([0-9]*\).*/\1/')
    else ok=none; best=NA; fi
    printf "%s\t%s\t%s\t%s\t%s\n" "$b" "$best" "$ok" "$T" "$desc" >> squad/r1/c4/ls_results.tsv
  done < $g/est.txt
done
echo LS_DONE
