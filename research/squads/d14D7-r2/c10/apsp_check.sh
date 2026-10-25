#!/bin/bash
# Independent check of the type-2 cell for (9,7): edge list from unit_edges2.py, then apsp_cyc (all-pairs by copies).
# usage: apsp_check.sh K   (K = 1 or 2: uses cells2/c10_pk$K.* copied into c10/)
U=/home/user/degree-diameter/research/cell147/units
C=/home/user/degree-diameter/research/squads/d14D7-r2/c10
GH=/home/user/degree-diameter/research/cell147/data/gh_7.txt
K=$1
cd $U || exit 1
python3 unit_edges2.py $GH $C/c10_pk$K.state $C/c10_pk$K.units $C/c10_pk$K.x $C/c10_pk$K.edges || exit 1
head -1 $C/c10_pk$K.edges
NB=117648 ./apsp_cyc $C/c10_pk$K.edges 9 7 3 1
echo "apsp rc=$?"
