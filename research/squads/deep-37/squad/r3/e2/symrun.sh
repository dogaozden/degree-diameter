#!/bin/bash
# usage: symrun.sh GROUPNAME SECS SEED  (chains from symbo/GROUPNAME_cur.edges, writes best back to cur)
D=/home/user/degree-diameter/research/squads/deep-37/squad/r3/e2
G=$1; S=$2; SEED=$3
cur=$D/symbo/${G}_cur.edges
nice -n 15 $D/symbobin $D/grp/$G.txt $cur $S $SEED $D/symbo/${G}_s$SEED 2>/dev/null | tail -1
if [ -f $D/symbo/${G}_s${SEED}_best.edges ]; then cp $D/symbo/${G}_s${SEED}_best.edges $D/symbo/${G}_cur.edges; fi
