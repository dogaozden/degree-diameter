#!/bin/bash
# card c9, second pass: try K=33 flags (kpack, then kpack2); if solved, run the full t2cell check and the apsp_cyc check.
C9=/home/user/degree-diameter/research/squads/d14D7-r2/c9
GH=/home/user/degree-diameter/research/cell147/data/gh_5.txt
cd $C9
rm -f m33a.flags m33b.flags
$C9/kpack $GH 33 50 31 $C9/m33a.flags > $C9/m33a.log 2>&1
if [ ! -f $C9/m33a.flags ]; then $C9/kpack2 $GH 33 50 32 $C9/m33b.flags > $C9/m33b.log 2>&1; fi
FL=""
if [ -f $C9/m33a.flags ]; then FL=$C9/m33a.flags; elif [ -f $C9/m33b.flags ]; then FL=$C9/m33b.flags; fi
if [ -z "$FL" ]; then echo "K=33 not solved" > $C9/second_pass.txt; exit 0; fi
echo "K=33 solved: $FL" > $C9/second_pass.txt
cd /home/user/degree-diameter/research/cell147/units
./t2cell.sh c9_k33 $GH 1 7 1 1 $FL > $C9/t2cell_k33.out 2>&1
echo "t2cell rc=$?" >> $C9/t2cell_k33.out
python3 unit_edges2.py $GH cells2/c9_k33.state cells2/c9_k33.units cells2/c9_k33.x $C9/c9_k33.edges > $C9/edges33.out 2>&1
NB=23436 ./apsp_cyc $C9/c9_k33.edges 7 7 3 1 > $C9/apsp33.out 2>&1
echo "apsp rc=$?" >> $C9/apsp33.out
