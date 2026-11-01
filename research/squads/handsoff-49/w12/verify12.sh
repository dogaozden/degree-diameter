#!/bin/bash
# verify12.sh EDGES : independent all-pairs check at D=9 (must be VALID) and D=8 (must be INVALID) and degree/bipartite info
H=/home/user/degree-diameter/research/squads/handsoff-49
A=$H/tools/apsp
echo "D=9: $($A "$1" 4 9 | tr '\n' ' ')"
echo "D=8: $($A "$1" 4 8 | tail -1)"
