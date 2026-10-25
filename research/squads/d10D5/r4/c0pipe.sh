#!/bin/bash
# c0pipe.sh COV.sol "FDSET" TAG SEED: coset-0 stage for a coverage(+D1)-0 FLAGDEL state (hub-sourced failures 0):
# strict dmfast_fd3 pass, then two penalty passes (each from the previous best)
X=$1; FS=$2; T=$3; SD=${4:-1}; R=runs/$T
python3 ../hubs/sol2lift2.py "$X" ${R}_l2.sol > /dev/null
./c0run.sh $X ${R}_l2.sol "$FS" ${R}_c0a $SD 1 12000000 0.25 0.01 0.5 | tail -n 1
./c0run.sh $X ${R}_c0a.sol "$FS" ${R}_c0b $((SD + 1)) 2 10000000 0.15 0.03 0.6 | tail -n 1
./c0run.sh $X ${R}_c0b.sol "$FS" ${R}_c0c $((SD + 2)) 2 10000000 0.12 0.04 0.7 | tail -n 1
