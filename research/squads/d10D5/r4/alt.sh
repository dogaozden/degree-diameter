#!/bin/bash
# alt.sh STATE.sol START.lift2.sol "FDSET" TAG SEED ROUNDS: alternate a hub-aware dmfast penalty pass and a 10-minute
# lns3 FOCUS search, keeping the best state by true score (lns3 start line); prints the score after each stage.
X=$1; C=$2; FS=$3; T=$4; SD=$5; NR=${6:-6}; R=runs/$T
sc() { SECS=0 python3 lns3.py "$X" "$1" "$FS" /dev/null 2>&1 | grep start | awk '{print $2}'; }
cp "$C" ${R}_best.sol; best=$(sc ${R}_best.sol); echo "start $best"
for i in $(seq 1 $NR); do
  ./c0run.sh "$X" ${R}_best.sol "$FS" ${R}_d$i $((SD * 100 + i)) 2 8000000 0.14 0.04 0.7 > /dev/null
  [ -f ${R}_d$i.sol ] && s=$(sc ${R}_d$i.sol) || s=999; echo "round $i dmfast $s"
  [ "$s" -le "$best" ] 2>/dev/null && cp ${R}_d$i.sol ${R}_best.sol && best=$s
  FOCUS=1 CHEAP=1 FW=4 FT=0.6 RESET=25 SECS=600 STEP=20 SIZE=50 NPHI=150 NF1=6 KZ=8 SEED=$((SD * 100 + i)) timeout 700 nice -n 5 python3 lns3.py "$X" ${R}_best.sol "$FS" ${R}_l$i.sol > ${R}_l$i.log 2>&1
  [ -f ${R}_l$i.sol ] && s=$(sc ${R}_l$i.sol) || s=999; echo "round $i lns3 $s"
  [ "$s" -le "$best" ] 2>/dev/null && cp ${R}_l$i.sol ${R}_best.sol && best=$s
  [ "$best" = "0" ] && { echo FOUND; ./finish_fd.sh "$X" ${R}_best.sol "$FS" ${R}_fin | tail -n 1; break; }
done
echo "final best $best"
