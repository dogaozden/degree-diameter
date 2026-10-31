#!/bin/bash
# sub_runs.sh: breakout lift over subgroups of C2xC4 started from the far-256 graph (40 s each, lift3 INIT).
cd "$(dirname "$0")"
run(){ INIT=$1 POOL=8 PP=60 STALL=1500 FR=1 TEN=4 WCAP=16 nice -n 10 ./lift3 $2 $3 $4 $5 out/sub_$6 > out/sub_$6.log 2>&1; echo "$6 $(grep '^END' out/sub_$6.log | sed 's/.*best_raw=\([0-9]*\) far=\([0-9]*\).*/raw \1 far \2/')" >> out/sub_runs.tsv; }
run base/c2c4_C4b_k24.state groups/H_C4b.txt 24 811 40 C4b_s811
run base/c2c4_C2C2_k24.state groups/H_C2C2.txt 24 812 40 C2C2_s812
echo SUB_DONE >> out/sub_runs.tsv
