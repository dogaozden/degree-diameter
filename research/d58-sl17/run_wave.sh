#!/bin/bash
# job d58-sl17: plain annealing on SL(2,17), d=5, D=8, K=8 candidates per step; one line per seed in jobs.txt
# usage: run_wave.sh jobs.txt   (each line: seed secs)
HERE=/home/user/degree-diameter/research/d58-sl17
cat "$1" | xargs -P 4 -L 1 bash -c 'seed=$0; secs=$1; \
  DUMP='"$HERE"'/runs/dump_s${seed}.txt DUMPMAX=1 \
  '"$HERE"'/src/sl17 5 8 ${secs} ${seed} 8 '"$HERE"'/runs/sol_s${seed}.txt sl 17 1 \
  > '"$HERE"'/logs/sl17_s${seed}.log 2>&1'
