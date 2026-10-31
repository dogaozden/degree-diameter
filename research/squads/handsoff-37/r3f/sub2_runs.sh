#!/bin/bash
# sub2_runs.sh: breakout lift over the involution subgroups of C2xC4 (base 48+48), 40 s each, from the far-256 graph.
cd "$(dirname "$0")"
for g in C2a C2b; do
  INIT=base/c2c4_${g}_k48.state POOL=8 PP=60 STALL=1500 FR=1 TEN=4 WCAP=16 nice -n 10 ./lift3_64 groups/H_$g.txt 48 821 40 out/sub2_$g > out/sub2_$g.log 2>&1
  echo "$g $(grep '^END' out/sub2_$g.log | sed 's/.*best_raw=\([0-9]*\) far=\([0-9]*\).*/raw \1 far \2/')" >> out/sub2_runs.tsv
done
echo SUB2_DONE >> out/sub2_runs.tsv
