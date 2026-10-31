#!/bin/bash
# usage: run_seeds.sh SECS SEEDS "gid:p:name gid:p:name ..."   (one salift process at a time, skips finished seeds)
cd /home/user/degree-diameter/research/squads/handsoff-37/r2a
SECS=$1; SEEDS=$2; shift 2
for spec in $1; do
  IFS=: read gid p name <<< "$spec"
  for s in $(seq 1 $SEEDS); do
    f=seeds160/g${gid}_${name}_s${s}.edges
    [ -s "$f" ] && continue
    sol=seeds160/g${gid}_${name}_s${s}.sol
    timeout 120 nice -n 10 ./salift $p groups.tab $gid $((s*1000+gid)) $SECS 10 0.3 $sol > logs/n160_salift_g${gid}_s${s}.log 2>&1
    if [ -s "$sol" ]; then
      python3 lift2edges.py groups.tab $sol > $f
      r=$(./score37 $f); echo "$name g$gid s$s : $r"
      echo "$name g$gid s$s far0" >> logs/n160_found.txt
    else
      echo "$name g$gid s$s : not found in $SECS s (best $(grep best logs/n160_salift_g${gid}_s${s}.log | tail -1))"
    fi
  done
done
