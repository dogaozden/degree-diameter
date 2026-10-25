#!/bin/bash
# expand_score.sh GRAPHTAG QSOL OUT: expand a quotient solution (qF_<tag> map) to orbit-graph indices and score it.
set -e
R=/home/user/degree-diameter/research/squads/d16D7_r3
S=/home/user/degree-diameter/research/squads
TAG=$1; QSOL=$2; OUT=$3
python3 -I $S/cells/d16D7/ogquot_expand.py $R/quot/qF_$TAG.map $QSOL $OUT
python3 -I $S/d16D7_r2/ogscore.py $S/d16D7_r2/og_$TAG.txt $OUT
