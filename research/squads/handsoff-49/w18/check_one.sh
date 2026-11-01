#!/bin/bash
# check_one.sh FILE OUTPREFIX : runs score48 and apsp (both at d=4 D=9) on one edge list, saves raw output
H=/home/user/degree-diameter/research/squads/handsoff-49
F="$1"; O="$2"
nice -n 10 timeout 300 $H/tools/score48 "$F" 4 9 > "$O.score" 2>&1
nice -n 10 timeout 300 $H/tools/apsp "$F" 4 9 > "$O.apsp" 2>&1
