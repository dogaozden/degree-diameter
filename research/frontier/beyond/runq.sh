#!/bin/bash
# runq.sh QUEUE: run hq.sh on each line "d D secs seed K fam p n k m f" in order, log to runs/QUEUE.log
cd "$(dirname "$0")"
while read d D secs seed K fam p n k m f; do
  [ -z "$d" ] && continue
  echo "$(date -u +%T) start $d $D $fam $p $n orbit $k $m $f" >> runs/$1.log
  ./hq.sh $d $D $secs $seed $K $fam $p $n "$k $m $f" 2 >> runs/$1.log 2>&1
  echo "$(date -u +%T) end" >> runs/$1.log
done < $1
echo "$(date -u +%T) QUEUE DONE" >> runs/$1.log
