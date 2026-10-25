#!/bin/bash
# like r3/alt_run10.sh but with r3/alt_opt2.sh and MAXC=8 (screen first, alternate only near misses)
g=$1
MAXC=8 r3/alt_opt2.sh 2 5 bases5/k5r1_000.txt r3/gtab/$g.txt r3/k5q2_c5_216.txt 4 90 120 r3/alt/d10_$g > r3/alt/d10_$g.log 2>&1
echo "$g: $(tail -n 1 r3/alt/d10_$g.log)"
