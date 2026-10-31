#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-65/c4
while read n i; do ./sweep_diag.sh sa 2 6 6 $n $i </dev/null; done < tasks2f.txt
echo DONE2F >> results.txt
