#!/bin/bash
# diagonal pairs only (H = K as conjugacy classes), tasks2.txt from line 8 on
cd /home/user/degree-diameter/research/squads/handsoff-65/c4
while read n i; do ./sweep_diag.sh sa 2 6 6 $n $i </dev/null; done < tasks2e.txt
echo DONE2 >> results.txt
