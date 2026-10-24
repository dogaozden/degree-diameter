#!/bin/bash
# run_c13.sh: one heavy slot for the whole c13 chain (fewer slot waits): (1) QUICK check of the baseline c13_s1
# (cells2/c13_s1.* from t2cell.sh, hub graph from hub13.py), (2) SA packing of flags for one matching (pack, 200 CPU s),
# (3) CHECKONLY validation of the flags, (4) final13.sh build + QUICK check with those flags.
C=/home/user/degree-diameter/research/squads/d14D7-r2/c13
U=/home/user/degree-diameter/research/cell147/units
cd $U || exit 1
ONLYUNITS=1 ./uhcheck ../data/gh_11.txt cells2/c13_s1.state cells2/c13_s1.units $C/c13_s1.hub13.x 7 1 > $C/c13_s1.uhcheck.txt 2> $C/c13_s1.uhcheck.log
echo "rc=$?" >> $C/c13_s1.uhcheck.log
./pack ../data/gh_11.txt 200 1 $C/c13_packA_s1.flags 2> $C/c13_packA_s1.log
CHECKONLY=1 ./pack ../data/gh_11.txt 0 1 /dev/null $C/c13_packA_s1.flags
$C/final13.sh c13_pA $C/c13_packA_s1.flags 1
echo "chain done"
