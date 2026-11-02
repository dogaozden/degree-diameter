#!/bin/bash
# usage: run.sh SEED   -- one 90 s plain-S annealing run on meta 1559 41 84 (N = 63,919, 2N = 127,838)
# knob by seed index i = SEED - 3001: i%4 in {0,1}: K=16 TARGP=70 ; i%4==2: K=4 TARGP=70 ; i%4==3: K=16 TARGP=90
B=/home/user/degree-diameter/research/squads/raise9/bin
W=/home/user/degree-diameter/research/squads/raise9/r3/g2
cd "$W" || exit 1
S=$1
i=$((S-3001))
case $((i%4)) in
  0|1) K=16; TP=70 ;;
  2) K=4; TP=70 ;;
  3) K=16; TP=90 ;;
esac
OUTF=OUT_s${S}.txt
ERRF=log_s${S}.txt
THREADS=1 TARGP=$TP SAVEBEST=b_s${S}.txt timeout 105 nice -n 10 $B/haar_gen3s 6 9 90 $S $K $OUTF meta 1559 41 84 1 > res_s${S}.txt 2> $ERRF
RL=$(grep RESULT res_s${S}.txt)
BEST=$(echo "$RL" | sed -n 's/.*best=\([-0-9]*\).*/\1/p')
EV=$(echo "$RL" | sed -n 's/.*evals=\([0-9]*\).*/\1/p')
if [ -f "$OUTF" ]; then SOLVED=YES; else SOLVED=no; fi
echo "$S | K=$K | TARGP=$TP | best=${BEST:-NA} | evals=${EV:-NA} | solved=$SOLVED" | tee -a seeds.txt
echo "last progress: $(tail -1 $ERRF)"
