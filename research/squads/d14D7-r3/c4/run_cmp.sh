#!/bin/bash
# run_cmp.sh SECONDS SEED NAME [SEEDFILE]: one seeded (or random) ILS run through heavy.sh, THREADS=1
cd /home/user/degree-diameter/research/squads/d14D7-r3/c4
S=$1; SD=$2; NM=$3; SF=$4
if [ -n "$SF" ]; then export SEEDS=$PWD/$SF; fi
THREADS=1 /home/user/degree-diameter/research/squads/bin/heavy.sh $((S+120)) ./seedils /home/user/degree-diameter/research/cell147/data/gh_11.txt /home/user/degree-diameter/research/cell147/data/coords11.txt 1 $S $SD $PWD/run_$NM.flags 2> run_$NM.log
echo "$NM exit=$?"
