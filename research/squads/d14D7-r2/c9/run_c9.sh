#!/bin/bash
# card c9: search a flag set for q=5 (K=36 by kpack2 if it solves in 40 s, else the 30-flag set k30.flags), then the
# full t2cell check (uhcheck), then an independent edge-list check (apsp_cyc). Outputs in this folder.
C9=/home/user/degree-diameter/research/squads/d14D7-r2/c9
GH=/home/user/degree-diameter/research/cell147/data/gh_5.txt
cd $C9
rm -f m36.flags
$C9/kpack2 $GH 36 40 21 $C9/m36.flags > $C9/m36.log 2>&1
FL=$C9/k30.flags
if [ -f $C9/m36.flags ]; then FL=$C9/m36.flags; fi
echo "using $FL" > $C9/chosen.txt
cd /home/user/degree-diameter/research/cell147/units
./t2cell.sh c9_best $GH 1 7 1 1 $FL > $C9/t2cell_best.out 2>&1
echo "t2cell rc=$?" >> $C9/t2cell_best.out
python3 unit_edges2.py $GH cells2/c9_best.state cells2/c9_best.units cells2/c9_best.x $C9/c9_best.edges > $C9/edges.out 2>&1
NB=23436 ./apsp_cyc $C9/c9_best.edges 7 7 3 1 > $C9/apsp.out 2>&1
echo "apsp rc=$?" >> $C9/apsp.out
