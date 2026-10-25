#!/bin/bash
# final13.sh NAME FLAGSFILE [SEED]: the t2cell.sh pipeline for cell (13,7) (q = 11, j = 1, m = 3, Delta = 13) with
# (i) type-2 units from FLAGSFILE (empty file = random scan packing, as in t2cell.sh with no flags), (ii) the c13 hub
# generator hub13.py in place of randhub.py (randhub.py fails for 76+ units at d = 10), (iii) QUICK uhcheck.
# Outputs: cells2/NAME.* in the units folder and c13/NAME.{x,uhcheck.txt,uhcheck.log,hub.log} in the card folder.
NAME=$1; FL=$2; SEED=${3:-1}
C=/home/user/degree-diameter/research/squads/d14D7-r2/c13
U=/home/user/degree-diameter/research/cell147/units
GH=../data/gh_11.txt
cd $U || exit 1
OUT=cells2/$NAME
python3 mkunits.py $GH 1 $SEED $OUT.rand.state /dev/null 2>/dev/null || exit 1
if [ -s "$FL" ]; then FLAGS=$FL BOTH=1 ./t2design $GH $OUT.rand.state 1 10000000 $OUT.state $OUT.units $SEED 2> $OUT.t2.log
else SCAN=1 ./t2design $GH $OUT.rand.state 1 10000000 $OUT.state $OUT.units $SEED 2> $OUT.t2.log; fi
NU=$(wc -l < $OUT.units)
python3 $C/hub13.py $NU 10 $SEED > $C/$NAME.x 2> $C/$NAME.hub.log || exit 1
ONLYUNITS=1 ./uhcheck $GH $OUT.state $OUT.units $C/$NAME.x 7 1 > $C/$NAME.uhcheck.txt 2> $C/$NAME.uhcheck.log
echo "$NAME: q=11 j=1 m=3 Delta=13 units=$NU n=$((2*177156*3 + 2*NU)) $(grep -oE 'pairs beyond D = [0-9]+' $C/$NAME.uhcheck.txt) $(cat $C/$NAME.hub.log)"
cp $OUT.units $C/$NAME.units; cp $OUT.state $C/$NAME.state
