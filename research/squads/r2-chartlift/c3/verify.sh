#!/bin/bash
# usage: verify.sh CTRL_FILE  (run from the chartlift tool dir). Builds the lift, checks diameter 5 and 4 with apsp, deletes the edge list.
F=/home/user/degree-diameter/research/squads/r2-chartlift/c3
CTRL=$1; E=$F/verify_$(basename $CTRL .ctrl).edges
python3 lift.py $CTRL r3/k5q3_pd112.txt 3 5 $E || exit 1
echo "d=5 check:"; timeout 900 nice -n 10 $F/apsp $E 15 5
echo "d=4 check:"; timeout 900 nice -n 10 $F/apsp $E 15 4
rm -f $E
