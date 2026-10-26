#!/bin/bash
# gentle.sh BASE.sol BASE.lift2.sol "FDSET" TAG SEED: convert one more flag starting from a VALID state's sigma/nu
# (no coverage-stage annealing): mkhubF (hub numbering, own-flag hub pairs) -> hub rewire if coverage holes ->
# lns2 exact sigma search on coverage + D1 + coset-0 routes together -> dmfast penalty passes -> report true cost.
B=$1; BL=$2; FS=$3; T=$4; SD=${5:-1}; R=runs/$T
python3 mkhubF.py "$B" "$FS" ${R}_k.sol $SD | tail -n 1
st=$(SECS=0 python3 lns3.py ${R}_k.sol "$BL" "$FS" /dev/null 2>&1 | grep start); echo "gentle start: $st"
if [ "$(echo $st | awk '{print $4}' | tr -d ',')" != "0" ]; then python3 rewire.py ${R}_k.sol "$FS" ${R}_k.sol "$BL" | tail -n 1; fi
KZ=4 SECS=${LSECS:-900} STEP=30 SIZE=40 SEED=$SD timeout $(( ${LSECS:-900} + 100 )) nice -n 5 python3 lns2.py ${R}_k.sol "$BL" "$FS" ${R}_g.sol > ${R}_g.log 2>&1
tail -n 1 ${R}_g.log
[ -f ${R}_g.sol ] || cp "$BL" ${R}_g.sol
./c0run.sh ${R}_k.sol ${R}_g.sol "$FS" ${R}_p1 $SD 2 6000000 0.08 0.05 0.7 | tail -n 1
