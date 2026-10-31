#!/bin/bash
# tabu parameter sweep on 176/17 a2: each config, seeds 21..23, 40 s each -> param.tsv
C1=/home/user/degree-diameter/research/squads/handsoff-65/c1; S=/home/user/degree-diameter/research/squads/handsoff-65/shared
G=$C1/tabs/sg_176_17.txt
run() { name=$1; shift
  for seed in 21 22 23; do
    r=$(env "$@" INIT=random SECS=40 SEED=$seed timeout 120 nice -n 10 $S/tabu $C1/bases/a2.base $G 2>/dev/null | grep RESULT | awk '{print $3}')
    printf '%s\tseed%s\t%s\n' "$name" "$seed" "${r:-NA}" >> $C1/param.tsv
  done; }
run default X=1
run long_tabu TMIN=15 TMAX=30
run short_tabu TMIN=3 TMAX=8
run tabuedge TABUEDGE=1 TMIN=5 TMAX=12
run kick_often STALL=600 KICK=4
echo PDONE >> $C1/param.tsv
