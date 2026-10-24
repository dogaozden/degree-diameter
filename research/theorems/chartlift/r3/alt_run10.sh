#!/bin/bash
# run r3/alt_opt.sh for one (10,5) Haar group (q=2, k=5, start chart r3/k5q2_c5_216.txt): r3/alt_run10.sh GROUPTAG
g=$1
r3/alt_opt.sh 2 5 bases5/k5r1_000.txt r3/gtab/$g.txt r3/k5q2_c5_216.txt 4 90 120 r3/alt/d10_$g > r3/alt/d10_$g.log 2>&1
echo "$g: $(tail -n 1 r3/alt/d10_$g.log)"
