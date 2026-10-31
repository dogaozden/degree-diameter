#!/bin/bash
# c1 beam over insertion + tabu repair.
# usage: beam.sh START_EDGES(file, n) LEVELS KEEP TABU_SECS TAG
# each level: insert a pair (k=2, a~b) into every kept graph (all edge pairs), keep top KEEP by far (insert writes
# TOPK files per base), repair each kept graph with tabu3 (MODE 2, TT 10) for TABU_SECS, keep the repaired best KEEP.
START=$1; LEVELS=$2; KEEP=$3; TSEC=$4; TAG=$5
mkdir -p beam_$TAG
cp "$START" beam_$TAG/L0_000_best.edges
for L in $(seq 1 $LEVELS); do
  P=beam_$TAG/pool$L; mkdir -p $P; rm -f $P/*.edges
  for f in beam_$TAG/L$((L-1))_*_best.edges; do
    b=$(basename $f .edges)
    nice -n 10 ./insert $f 2 0 $KEEP $P/$b > /dev/null 2>&1
  done
  # pick best KEEP from pool by far (file name carries far)
  ls $P/*.edges | while read -r e; do far=$(echo $e | sed 's/.*_far\([0-9]*\)\.edges/\1/'); echo "$far $e"; done | sort -n | head -$KEEP > beam_$TAG/cand$L.txt
  i=0; : > beam_$TAG/rep$L.txt
  while read -r far e; do
    i=$((i+1)); o=beam_$TAG/L${L}_$(printf %03d $i)
    nice -n 10 timeout 560 ./tabu3 $e 100000000 10 $i $o 2 $TSEC > beam_$TAG/log_L${L}_$i.txt 2>&1
    echo "$i $(tail -1 beam_$TAG/log_L${L}_$i.txt)" >> beam_$TAG/rep$L.txt
  done < beam_$TAG/cand$L.txt
  echo "level $L done $(date -u +%T)"; cat beam_$TAG/rep$L.txt
done
