#!/bin/bash
# usage: run.sh TODOFILE TAG   (run from research/s65/c3p256/rank2): C3 x P256 non-Haar |H|=2 bi-coset graphs for the
# rank-2 groups P (ids 1..541) not swept before; export in chunks of 30, anneal every pair 5 s; results_TAG.txt
T=$1; G=$2; mkdir -p d_$G
split -l 30 -d $T chunk_${G}_
for c in chunk_${G}_*; do
  ids=$(tr '\n' ',' < $c | sed 's/,$//')
  gap -q -c "PORD:=256; IDS:=[$ids]; OUTDIR:=\"d_$G\";" c3p_export.g > /dev/null 2>&1
  for f in d_$G/*.dc2; do [ -e "$f" ] || continue
    r=$(SA=1 SECS=5 SEED=1 timeout 120 nice -n 4 ../../tools/dcenum $f 6 5 $f.edges 2>/dev/null | grep -o 'best [0-9]*' | awk '{print $2}')
    echo "$(basename $f) $r" >> results_$G.txt
    if [ -n "$r" ] && [ "$r" -le 30 ]; then mkdir -p keep; mv $f $f.edges keep/ 2>/dev/null; else rm -f $f $f.edges; fi
  done
  echo "$c done $(date -u +%H:%M:%S)" >> progress_$G.txt
done
echo DONE >> progress_$G.txt
