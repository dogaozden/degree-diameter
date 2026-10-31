#!/bin/bash
# usage: batch_tabu.sh TAG STEPS TT R TLIM START1 [START2 ...]   (sequential, one process at a time)
TAG=$1; STEPS=$2; TT=$3; R=$4; TL=$5; shift 5
i=0
for f in "$@"; do
  i=$((i+1))
  nice -n 10 timeout 560 ./tabu2sw "$f" "$STEPS" "$TT" $i out/${TAG}_$i $R $TL > logs/${TAG}_$i.log 2>&1
  echo "$TAG $i $(basename $f) $(tail -1 logs/${TAG}_$i.log)"
done
