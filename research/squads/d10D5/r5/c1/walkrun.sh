#!/bin/bash
# walkrun.sh P SEED TABU SECS NAME [ITERS]: WalkSAT run from S5 (c0run.sh environment), output r5/c1/NAME.sol (lift2)
R4=/home/user/degree-diameter/research/squads/d10D5/r4; R5=/home/user/degree-diameter/research/squads/d10D5/r5
P=$1; SD=$2; TB=$3; SC=$4; N=$5; IT=${6:-3000000}
cd $R4 && FREE="$(awk '$1=="free"{$1="";print}' $R5/S5.sol)" FDSET="1 6 5" RELAX=2 PENW=2 HUBADJ="$(python3 hubadj.py $R5/S5.sol "1 6 5")" \
  BASE=gq/gq_q7.bin NPOLY=4 SEED=$SD IN=$R5/S5_c0.lift2.sol OUT=$R5/c1/$N.lift2.sol PTARG=0.6 SWAPP=0.02 ITERS=$IT TEMP0=0.12 TEMP1=0.02 \
  WALK=$P TABU=$TB SECS=$SC nice -n 10 timeout 1500 $R5/c1/dmwalk 7 > $R5/c1/$N.log 2> $R5/c1/$N.err
tail -n 1 $R5/c1/$N.log; grep -c . $R5/c1/$N.err >/dev/null
