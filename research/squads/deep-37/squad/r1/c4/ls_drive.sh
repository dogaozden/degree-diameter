#!/bin/bash
# ls_drive.sh SECS GROUPKEY... : for each G-set file of the groups (up to 3 SAT-feasible families per group),
# build a G-invariant cubic start (mkstart.py) and run breakout search (symbo) for SECS seconds; log to ls_results.tsv
cd /home/user/degree-diameter/research/squads/deep-37
T=$1; shift
for g in "$@"; do
  k=0
  for f in $(ls squad/r1/c4/gs/n170/g${g}/f_[0-9]*.txt 2>/dev/null | sort -t_ -k2 -n); do
    [ $k -ge 3 ] && break
    b=$(basename $(dirname $f))_$(basename $f .txt)
    st=squad/r1/c4/st/$b.edges
    r=$(timeout 30 nice -n 15 python3 squad/r1/c4/mkstart.py $f $st 1 2>&1 | tail -1)
    case "$r" in UNSAT*) continue;; esac
    [ -f $st ] || continue
    k=$((k+1))
    out=squad/r1/c4/ls/$b
    timeout 100 nice -n 15 squad/r1/c4/symbo $f $st $T 1 $out > $out.log 2>&1
    best=$(bin/score37 ${out}_best.edges 2>&1 | tail -1 | sed 's/.*far=\([0-9]*\).*/\1/')
    echo -e "$b\t$(grep -o 'A:.*' $(dirname $f)/est.txt | head -0)$best\t$T" >> squad/r1/c4/ls_results.tsv
  done
done
echo LS_DONE
