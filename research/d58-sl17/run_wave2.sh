#!/bin/bash
# job d58-sl17 wave 2: each line of the job file is "seed secs tmax initfile|-" ; tmax = starting temperature (TMAX),
# initfile = INIT state (5 matrix lines) or - for a random start. Four jobs at a time.
HERE=/home/user/degree-diameter/research/d58-sl17
cat "$1" | xargs -P 4 -L 1 bash -c 'seed=$0; secs=$1; tmax=$2; init=$3; \
  if [ "$init" = "-" ]; then INITENV=""; else INITENV="INIT=$init"; fi; \
  env $INITENV TMAX=$tmax TMIN=0.15 DUMP='"$HERE"'/runs/dump_w2_s${seed}.txt DUMPMAX=1 \
  '"$HERE"'/src/sl17 5 8 ${secs} ${seed} 8 '"$HERE"'/runs/sol_w2_s${seed}.txt sl 17 1 \
  > '"$HERE"'/logs/w2_s${seed}.log 2>&1'
