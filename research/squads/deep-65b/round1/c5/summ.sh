#!/bin/sh
# prints: order id a best_cost iters  (from screen.txt)
awk '{ match($0,/best_cost=[0-9]+/); bc=substr($0,RSTART+10,RLENGTH-10); match($0,/iters=[0-9]+/); it=substr($0,RSTART+6,RLENGTH-6); print $1, $2, $3, bc, it }' /home/user/degree-diameter/research/squads/deep-65b/round1/c5/screen.txt
