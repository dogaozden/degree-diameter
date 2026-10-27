#!/bin/bash
# usage: runone.sh NAME RFILE SEED TIMEOUT_EXT
D=/home/user/degree-diameter/research/projects/hexagon-family/ext
C=/home/user/degree-diameter/research/squads/hexfam_r3/c4
NAME=$1; RF=$2; SEED=$3; TO=${4:-300}
cd $C
timeout $TO nice -n 10 python3 $D/extend5.py 13 $RF /home/user/degree-diameter/research/d10D7/sets/L13_spread.txt $C/$NAME.pairs $SEED ${NS:-30000} 600 2 > $C/$NAME.log 2>&1
echo "ext exit $?" >> $C/$NAME.log
timeout 200 nice -n 10 python3 $D/mixsol.py 13 $C/$NAME.pairs $C/chk_$NAME 1 3 > $C/$NAME.chk 2>&1
echo "$NAME: $(grep -E 'RESULT|added' $C/$NAME.log | tail -1) | $(grep -E 'Lemma|verified|Error|assert' $C/$NAME.chk | tr '\n' ' ')"
rm -f $C/chk_$NAME.sol
