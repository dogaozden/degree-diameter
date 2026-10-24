#!/bin/bash
# run_c13b.sh: warm-start refinement of the 81-flag set c13_packA_s1.flags (pack with INFLAGS; cold start T0=0.05 so that the set is not melted; 120 CPU s),
# then CHECKONLY and the final13.sh build + QUICK check with the refined flags.
C=/home/user/degree-diameter/research/squads/d14D7-r2/c13
U=/home/user/degree-diameter/research/cell147/units
cd $U || exit 1
T0=0.05 T1=0.02 LAM0=2.0 LAM1=4.0 ./pack ../data/gh_11.txt 120 2 $C/c13_packR_s2.flags $C/c13_packA_s1.flags 2> $C/c13_packR_s2.log
CHECKONLY=1 ./pack ../data/gh_11.txt 0 1 /dev/null $C/c13_packR_s2.flags
$C/final13.sh c13_pR $C/c13_packR_s2.flags 2
echo "chain B done"
