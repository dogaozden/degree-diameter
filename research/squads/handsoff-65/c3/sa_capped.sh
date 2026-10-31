#!/bin/bash
# usage: sa_capped.sh RESULTSFILE SECS : simulated annealing over unions for files whose exhaustive search was capped
C3=/home/user/degree-diameter/research/squads/handsoff-65/c3
SH=/home/user/degree-diameter/research/squads/handsoff-65/shared
grep "tested 300000" $1 | sed 's/ :: .*//' | while read b; do
  f=$C3/out/$b.dc
  [ -f "$f" ] || continue
  r=$(SA=1 SECS=$2 ITERS=20000 SEED=7 timeout 600 nice -n 10 $SH/dcenum "$f" 6 5 "$C3/out/$b.sa.edges" 2>/dev/null | grep RESULT)
  echo "$b SA :: $r" | sed 's#/home/user/degree-diameter/research/squads/handsoff-65/c3/##g' | cut -c1-220
done
