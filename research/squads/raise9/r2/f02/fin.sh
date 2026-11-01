#!/bin/bash
# usage: fin.sh FROMTAG SEED SECS  -> finisher haar_gen3t resumed from b_FROMTAG.txt
B=/home/user/degree-diameter/research/squads/raise9/bin
D=/home/user/degree-diameter/research/squads/raise9/r2/f02
F=$1; SEED=$2; SECS=$3
cd $D
START=$D/b_$F.txt SAVEBEST=$D/b_fin_$F.txt OUT=x TFULL=1 TARGP=100 THREADS=1 timeout 105 nice -n 10 $B/haar_gen3t 6 9 $SECS $SEED 8 $D/OUT_fin_$F.txt meta 1559 41 84 1 > $D/log_fin_$F.txt 2>&1
echo "fin $F seed=$SEED : $(grep RESULT $D/log_fin_$F.txt)" | tee -a $D/log.txt
