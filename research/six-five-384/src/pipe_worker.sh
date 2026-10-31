#!/bin/bash
# pipe_worker.sh W: worker half of the pipeline. Claims the lowest-numbered queued export (atomic mv), expands it with
# hxexpand, runs haarex5, writes logs/h384_<id>.log (without PAIR lines, plus SECS), deletes the files. Stops when
# $Q/EXPORT_DONE exists and the queue is empty. Run from research/six-five-384. Env: Q, HX, HXE (hxexpand), TMPD.
set -u
w=$1; d=$TMPD/w$w; mkdir -p $d
while true; do
  f=$(ls $Q 2>/dev/null | grep '^pc_384_' | sort -t_ -k3 -n | head -1)
  if [ -z "$f" ]; then [ -e $Q/EXPORT_DONE ] && break; sleep 1; continue; fi
  mv $Q/$f $d/$f 2>/dev/null || continue
  i=${f#pc_384_}; i=${i%.txt}
  if ! $HXE $d/$f $d/hx_$i.txt; then echo "EXPANDFAIL $i" >> logs/failures.txt; rm -f $d/$f $d/hx_$i.txt; continue; fi
  s=$(date +%s.%N)
  $HX $d/hx_$i.txt | grep -v '^PAIR' > logs/h384_$i.tmp
  e=$(date +%s.%N)
  echo "SECS $(echo "$e - $s" | bc)" >> logs/h384_$i.tmp
  mv logs/h384_$i.tmp logs/h384_$i.log
  rm -f $d/$f $d/hx_$i.txt
done
