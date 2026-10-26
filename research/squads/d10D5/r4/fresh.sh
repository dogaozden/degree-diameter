#!/bin/bash
# fresh.sh "FDSET" TAG SEED: full conversion pipeline with the corrected (FLAGDEL coverage) and hub-aware tools, from
# the valid 4,840 state: mkhubF -> fdrun (coverage + D1, dmhub2_f) -> rewire if holes -> lns2 NOC0 if still holes ->
# three dmfast_fd3 coset-0 passes -> lns3 FOCUS (FW=4, FT=1.0) endgame.  True cost printed after each stage.
FS=$1; T=$2; SD=$3; R=runs/$T; B=${BASE:-../hubs/graphs/d10D5_n4840_flagdel2}
sc() { SECS=0 python3 lns3.py "$1" "$2" "$FS" /dev/null 2>&1 | grep start; }
python3 mkhubF.py $B.sol "$FS" ${R}_k.sol $SD | tail -n 1
./fdrun.sh ${R}_k.sol "$FS" ${R}_f $SD 300 0.2 > /dev/null
python3 ../hubs/sol2lift2.py ${R}_f.sol ${R}_f_l2.sol > /dev/null
echo "after fdrun: $(sc ${R}_f.sol ${R}_f_l2.sol)"
python3 rewire.py ${R}_f.sol "$FS" ${R}_f.sol ${R}_f_l2.sol | tail -n 1
st=$(sc ${R}_f.sol ${R}_f_l2.sol); echo "after rewire: $st"
cov=$(echo "$st" | awk '{gsub(/[(),]/," "); print $4+$5}')
if [ "$cov" != "0" ]; then NOC0=1 KZ=6 SECS=600 STEP=15 SIZE=60 SEED=$SD timeout 700 nice -n 5 python3 lns2.py ${R}_f.sol ${R}_f_l2.sol "$FS" ${R}_n.sol > ${R}_n.log 2>&1; [ -f ${R}_n.sol ] && cp ${R}_n.sol ${R}_f_l2.sol; echo "after lns2 NOC0: $(sc ${R}_f.sol ${R}_f_l2.sol)"; fi
./c0run.sh ${R}_f.sol ${R}_f_l2.sol "$FS" ${R}_c0a $SD 1 12000000 0.25 0.01 0.5 | tail -n 1
./c0run.sh ${R}_f.sol ${R}_c0a.sol "$FS" ${R}_c0b $((SD + 1)) 2 10000000 0.15 0.03 0.6 | tail -n 1
./c0run.sh ${R}_f.sol ${R}_c0b.sol "$FS" ${R}_c0c $((SD + 2)) 2 10000000 0.12 0.04 0.7 | tail -n 1
C=${R}_c0c.sol; [ -f $C ] || C=${R}_c0b.sol; [ -f $C ] || C=${R}_c0a.sol
echo "before endgame ($C): $(sc ${R}_f.sol $C)"
FOCUS=1 CHEAP=1 FW=4 FT=1.0 RESET=40 SECS=${ESECS:-2400} STEP=20 SIZE=50 NPHI=150 NF1=6 KZ=8 SEED=$SD timeout $(( ${ESECS:-2400} + 100 )) nice -n 5 python3 lns3.py ${R}_f.sol $C "$FS" ${R}_end.sol > ${R}_end.log 2>&1
tail -n 1 ${R}_end.log
