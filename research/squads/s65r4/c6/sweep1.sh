#!/bin/bash
# run bicay SA over triples; one process at a time
cd /home/user/degree-diameter/research/squads/s65r4/c6
BC=/home/user/degree-diameter/research/s65/groups/bc
T=/home/user/degree-diameter/research/s65/tools/bicay
while read f a b; do
  t0=$(date +%s.%N)
  out=$(A=$a B=$b MODE=sa SECS=4 SEED=1 timeout 60 nice -n 10 $T $BC/$f 2>&1)
  c=$(echo "$out" | grep '^RESULT best' | awk '{print $3}')
  best=$(echo "$out" | grep '^BEST' | head -1)
  [ -z "$c" ] && c=NA
  printf "%s\t%s\t%s\t%s\t%s\n" "$f" "$a" "$b" "$c" "$best" >> table1.tsv
done < triples1.txt
echo DONE >> table1.tsv
