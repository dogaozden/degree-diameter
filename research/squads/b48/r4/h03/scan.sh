#!/bin/bash
# h03: exhaustive 2+2 cubic lift scan of one group at (3,10); voltages a over conjugacy-class reps, b and c over all
T=/home/user/degree-diameter/research/squads/b48/tools
H=/home/user/degree-diameter/research/squads/b48/r4/h03
G=$1; name=$(basename $G .bin)
python3 $H/reps.py $G > $H/res/$name.reps || exit 1
s=$(date +%s.%N)
$H/gen < $H/res/$name.reps | LIMIT=8 ONLYLOW=1 timeout 300 nice -n 10 $T/flift $T/bases/cubic/b22_cubic.txt $G 3 10 eval > $H/res/$name.out 2> $H/res/$name.err
e=$(date +%s.%N)
echo "$name $(head -c 40 $H/res/$name.reps | cut -d' ' -f1-2) min: $(tail -1 $H/res/$name.err) lines: $(wc -l < $H/res/$name.out) secs: $(echo "$e - $s" | bc)"
