#!/bin/bash
# usage: beam_step.sh BASE_FILE_LIST TAG KEEP  -> inserts a pair (k=2 with a~b, all edge pairs) into each base,
# collects the best graphs of all bases into out/TAG_pool/ and prints the sorted far values.
LIST=$1; TAG=$2; KEEP=$3
mkdir -p out/${TAG}_pool
rm -f out/${TAG}_pool/*.edges
while read -r f; do
  b=$(basename "$f" .edges)
  nice -n 10 ./insert "$f" 2 0 $KEEP out/${TAG}_pool/${b}_ins > /dev/null 2>&1
done < "$LIST"
ls out/${TAG}_pool/*.edges | while read -r e; do far=$(echo "$e" | sed 's/.*_far\([0-9]*\)\.edges/\1/'); echo "$far $e"; done | sort -n | head -$KEEP
