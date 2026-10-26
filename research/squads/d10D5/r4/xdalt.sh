#!/bin/bash
# xdalt.sh STATE.sol START.lift2.sol "FDSET" "XDEL" TAG SEED ROUNDS: endgame for states with ordinary deleted flags.
# Alternates a dmgen penalty pass (GEN=1: coset-0 + 2 x holes, sigma and nu) and a nu-only lns3 FOCUS search (sigma
# fixed, so holes cannot reopen); keeps the best by (holes, coset-0) from dmgen's exact count; exact check at 0.
X=$1; C=$2; FS=$3; XD=$4; T=$5; SD=$6; NR=${7:-6}; R=runs/$T
HA="$(python3 hubadj.py $X "$FS")"; FR="$(awk '$1=="free"{$1="";print}' $X)"
sc() { FREE="$FR" FDSET="$FS" XDEL="$XD" GEN=1 RELAX=2 PENW=2 HUBADJ="$HA" BASE=gq/gq_q7.bin NPOLY=4 SEED=1 IN=$1 OUT=/dev/null PTARG=0 SWAPP=0 ITERS=1 TEMP0=0.1 TEMP1=0.02 ./dmgen 7 2>&1 | awk '/initial cost/ {c=$11} /penalty/ {h=$5} END {gsub(",","",h); print c + 100 * h}'; }
cp "$C" ${R}_best.sol; best=$(sc ${R}_best.sol); echo "start $best (coset-0 + 100 x holes)"
for i in $(seq 1 $NR); do
  FREE="$FR" FDSET="$FS" XDEL="$XD" GEN=1 RELAX=2 PENW=2 HUBADJ="$HA" BASE=gq/gq_q7.bin NPOLY=4 SEED=$((SD * 100 + i)) IN=${R}_best.sol OUT=${R}_d$i.sol PTARG=0.6 SWAPP=0.05 PHOLE=0.8 ITERS=3000000 TEMP0=0.12 TEMP1=0.03 timeout 2400 nice -n 5 ./dmgen 7 > ${R}_d$i.log 2> ${R}_d$i.err
  s=$(sc ${R}_d$i.sol); echo "round $i dmgen $s"; [ "$s" -le "$best" ] && cp ${R}_d$i.sol ${R}_best.sol && best=$s
  [ "$best" = "0" ] && break
  XDEL="$XD" FOCUS=1 CHEAP=1 FW=4 FT=0.6 RESET=25 SECS=600 STEP=30 SIZE=0 NPHI=300 NF1=10 KZ=0 SEED=$((SD * 100 + i)) timeout 700 nice -n 5 python3 lns3.py "$X" ${R}_best.sol "$FS" ${R}_l$i.sol > ${R}_l$i.log 2>&1
  [ -f ${R}_l$i.sol ] && s=$(sc ${R}_l$i.sol) || s=99999; echo "round $i lns3 $s"; [ "$s" -le "$best" ] && cp ${R}_l$i.sol ${R}_best.sol && best=$s
  [ "$best" = "0" ] && break
done
echo "final best $best"
[ "$best" = "0" ] && ./finish_xd.sh "$X" ${R}_best.sol "$FS" "$XD" ${R}_fin
