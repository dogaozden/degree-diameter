#!/bin/bash
# w6: turn a cost-0 Haar solution into an edge list, verify it, measure edge criticality, then run surgery annealing.
# usage: process_base.sh SOL TAG MODE SECONDS   (MODE 4: base n=4970 -> 4972 by 2 vertices; MODE 8: base n=4968 -> 4972)
H=/home/user/degree-diameter/research/squads/handsoff-49
W=$H/w6; T=$H/tools; cd $W
SOL=$1; TAG=$2; MODE=$3; SECS=$4
python3 $T/sol2edges.py $SOL bases/$TAG.edges || exit 1
echo "[$TAG] $($T/score48 bases/$TAG.edges 4 9 | tail -1)"
echo "[$TAG] edgecrit (vertex 0 edges = the 4 orbit representatives): $(nice -n 10 $T/edgecrit bases/$TAG.edges 9 0 4 2>/dev/null | tr '\n' ' ')"
if [ "$MODE" = "4" ]; then
  nice -n 10 ./surgsa2 bases/$TAG.edges bases/surg_$TAG.edges $SECS 31 4 6 0.5 2> bases/surg_$TAG.log | tail -1
else
  nice -n 10 ./surgsaK bases/$TAG.edges bases/surg_$TAG.edges $SECS 31 6 0.5 2> bases/surg_$TAG.log | tail -1
fi
echo "[$TAG] $(grep 'NEW BEST' bases/surg_$TAG.log | tail -1)"
echo "[$TAG] verify: $($T/score48 bases/surg_$TAG.edges 4 9 | tail -2 | tr '\n' ' ')"
