#!/bin/bash
# (7,5): exhaustive enumeration (all unions of double cosets of degree 7) of the |H| = 2 coset graphs of the best
# annealing near misses. usage: exh75.sh ORDER ID   -> logs/exh75_<order>_<id>.txt
cd "$(dirname "$0")"
o=$1; i=$2; d=tmpe_${o}_${i}_$$; mkdir -p $d
gap -q -c "ORDER:=$o; H_ORDER:=2; OUTDIR:=\"$d\"; IDS:=[$i];" sg_export.g > $d/gap.log 2>&1
for f in $d/*.dc2; do
  [ -e "$f" ] || continue
  r=$(nice -n 5 ./dcenum $f 7 5 ${f%.dc2}.edges 1000000000 2>&1 | tail -2 | tr '\n' ' ')
  echo "$r" >> logs/exh75_${o}_${i}.txt
  case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$(basename ${f%.dc2}).edges; cp $f logs/;; esac
done
rm -rf $d
echo "done $(date -u +%H:%M)" >> logs/exh75_${o}_${i}.txt
