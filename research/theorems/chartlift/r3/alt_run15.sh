#!/bin/bash
# run r3/alt_opt.sh for one (15,5) Haar group: r3/alt_run15.sh GROUPTAG
g=$1
r3/alt_opt.sh 3 5 bases5/k5r1_000.txt r3/gtab/$g.txt r3/k5q3_for168.txt 3 60 180 r3/alt/d15_$g > r3/alt/d15_$g.log 2>&1
echo "$g: $(tail -n 1 r3/alt/d15_$g.log)"
