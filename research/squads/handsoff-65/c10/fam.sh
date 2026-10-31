#!/bin/bash
# fam.sh L NAB SEED SECS T0 T1 : augment quotient base L (bases/q$L.base, bases/n$L.tab) by one pair, vl SA, log best
cd /home/user/degree-diameter/research/squads/handsoff-65/c10
L=$1; NAB=$2; SEED=$3; SECS=$4; T0=${5:-5}; T1=${6:-0.5}
M=$(head -1 bases/n$L.tab)
TAG=L${L}_n${NAB}_s${SEED}
python3 augment.py bases/q$L.base runs/$TAG.base $NAB $SEED 1 $M > /dev/null
N=$(( 2*M*0 ))
RES=$(SWAP=${SWAP:-0} FIXTREE=${FIXTREE:-0} T0=$T0 T1=$T1 SECS=$SECS SEED=$SEED ITERS=${ITERS:-100000000} OUT=runs/$TAG.sol timeout 300 nice -n 10 ../shared/vl runs/$TAG.base bases/n$L.tab 2>/dev/null | grep RESULT)
V=$(( $(head -1 runs/$TAG.base | cut -d' ' -f1) * M ))
echo -e "$TAG\tn=$V\t$RES" | tee -a runs/log.tsv
