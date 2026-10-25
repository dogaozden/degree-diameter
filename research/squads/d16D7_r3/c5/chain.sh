#!/bin/bash
# chain.sh FAM SIDE: quotient tabu (200 s CPU) -> expand -> score -> ktabu polish on the full orbit graph (420 s CPU)
# -> score. FAM = qhF or qhF2, SIDE = pts or lines. Heavy runs go through run_slot.sh.
FAM=$1; SIDE=$2
C5=/home/user/degree-diameter/research/squads/d16D7_r3/c5
R3=/home/user/degree-diameter/research/squads/d16D7_r3
R2=/home/user/degree-diameter/research/squads/d16D7_r2
CELLS=/home/user/degree-diameter/research/squads/cells/d16D7
QD=$R3/quot
cd $C5 || exit 1
TAG=${FAM}_${SIDE}
echo "== quotient search $TAG $(date +%T)"
$R3/run_slot.sh ./qtabu $QD/$TAG.txt seedq_$TAG.txt q_$TAG.sol 200 1 2> log_q_$TAG.txt
tail -3 log_q_$TAG.txt
python3 $CELLS/ogquot_expand.py $QD/$TAG.map q_$TAG.sol exp_$TAG.txt
python3 $R2/ogscore.py $R2/og_$SIDE.txt exp_$TAG.txt
echo "== polish $TAG $(date +%T)"
$R3/run_slot.sh $R2/c2/ktabu $R2/og_$SIDE.txt exp_$TAG.txt pol_$TAG.txt 420 1 2> log_pol_$TAG.txt
tail -3 log_pol_$TAG.txt
if [ -f pol_$TAG.txt ]; then python3 $R2/ogscore.py $R2/og_$SIDE.txt pol_$TAG.txt; else echo "polish wrote no larger set"; fi
echo "== done $TAG $(date +%T)"
