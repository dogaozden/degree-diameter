#!/bin/bash
# usage: mk.sh NAME "meta m k r" RULE M
D=/home/user/degree-diameter/research/squads/b48/r3/d12
T=/home/user/degree-diameter/research/squads/b48/tools
NAME=$1; SPEC=$2; RULE=$3; M=$4
timeout 120 nice -n 10 python3 $T/groups.py "$SPEC" $D/$NAME.bin >/dev/null
timeout 120 nice -n 10 python3 -I $D/mkphi.py $D/$NAME.bin $D/$NAME.phi $RULE $M
