#!/bin/bash
# c10 pipeline for (Delta,D) = (9,7): DGQ cover of H(7), j = 1 matching over Z_3, type-2 units.
# Runs inside one heavy.sh slot. Tools are run from the shared units folder (outputs c10_* in its cells2/).
U=/home/user/degree-diameter/research/cell147/units
C=/home/user/degree-diameter/research/squads/d14D7-r2/c10
GH=/home/user/degree-diameter/research/cell147/data/gh_7.txt
cd $U || exit 1
echo "== baseline random scan"; ./t2cell.sh c10_s1 $GH 1 9 1 1
echo "== pack SA (seed 11, 90 s)"; ./pack $GH 90 11 $C/pk1.flags 2> $C/pk1.err
echo "== pack GROW=200 + SA (seed 12, 90 s)"; GROW=200 ./pack $GH 90 12 $C/pk2.flags 2> $C/pk2.err
for k in 1 2; do
  echo "== check packing pk$k"; CHECKONLY=1 ./pack $GH 0 1 /dev/null $C/pk$k.flags
done
for k in 1 2; do
  echo "== type-2 cell with pk$k"; ./t2cell.sh c10_pk$k $GH 1 9 1 1 $C/pk$k.flags
  cp cells2/c10_pk$k.* $C/ 2>/dev/null
done
echo "== done"; date
