#!/bin/bash
# pipe_worker_gen.sh W: worker for pipe_export_gen.sh. Claims a queued pc_ORD_id.txt (expanded with hxexpand) or
# hx_ORD_id.txt, runs haarex5, writes $OUT/logs/h<ORD>_<id>.log (without PAIR lines, plus SECS). Stops when
# $Q/EXPORT_DONE exists and the queue is empty. Env: Q, OUT, HX, HXE, TMPD.
set -u
w=$1; d=$TMPD/g$w; mkdir -p $d $OUT/logs
while true; do
  f=$(ls $Q 2>/dev/null | grep -E '^(pc|hx)_[0-9]+_[0-9]+\.txt$' | head -1)
  if [ -z "$f" ]; then [ -e $Q/EXPORT_DONE ] && break; sleep 1; continue; fi
  mv $Q/$f $d/$f 2>/dev/null || continue
  g=${f#*_}; g=${g%.txt}
  if [ ${f%%_*} = pc ]; then
    if ! $HXE $d/$f $d/x_$g.txt; then echo "EXPANDFAIL $g" >> $OUT/failures.txt; rm -f $d/$f $d/x_$g.txt; continue; fi
    rm -f $d/$f
  else
    mv $d/$f $d/x_$g.txt
  fi
  s=$(date +%s.%N)
  $HX $d/x_$g.txt | grep -v '^PAIR' > $OUT/logs/h$g.tmp
  e=$(date +%s.%N)
  echo "SECS $(echo "$e - $s" | bc)" >> $OUT/logs/h$g.tmp
  mv $OUT/logs/h$g.tmp $OUT/logs/h$g.log
  rm -f $d/x_$g.txt
done
