#!/bin/bash
# tabu.sh STATE C0 "FDSET" "HARDPAIRS" TAG SEED ROUNDS: cumulative hard-pair walk.  Each round runs lns3 FOCUS with all
# hard pairs held good (the first bad hard pair is fixed by a kick), until it reaches a state with <= 1 bad pair; that
# pair is added to the hard list and the next round starts from that state.  Stops at 0 (exact check) or ROUNDS.
X=$1; C=$2; FS=$3; HP=$4; T=$5; SD=$6; NR=${7:-10}; R=runs/$T
cp "$C" ${R}_cur.sol
for i in $(seq 1 $NR); do
  HARDPAIR="$HP" FOCUS=1 CHEAP=1 FW=4 FT=0.6 RESET=30 SECS=900 STEP=20 SIZE=55 NPHI=180 NF1=8 KZ=10 SEED=$((SD * 100 + i)) \
    timeout 1000 nice -n 5 python3 lns3.py "$X" ${R}_cur.sol "$FS" ${R}_r$i.sol > ${R}_r$i.log 2>&1 &
  pid=$!
  while kill -0 $pid 2>/dev/null; do
    sleep 10
    if grep -qE "exact [01] \(.*\(cur [0-9]+\)" ${R}_r$i.log && [ -f ${R}_r$i.sol ]; then
      c=$(SECS=0 python3 lns3.py "$X" ${R}_r$i.sol "$FS" /dev/null 2>&1 | grep start | awk '{print $2}')
      if [ "$c" -le 1 ] 2>/dev/null; then kill $pid; break; fi
    fi
  done
  [ -f ${R}_r$i.sol ] || { echo "round $i: no state"; continue; }
  c=$(SECS=0 python3 lns3.py "$X" ${R}_r$i.sol "$FS" /dev/null 2>&1 | grep start | awk '{print $2}')
  bad=$(./whatbad.sh "$X" ${R}_r$i.sol "$FS")
  echo "round $i: cost $c bad: $bad"
  cp ${R}_r$i.sol ${R}_cur.sol
  if [ "$c" = "0" ]; then echo FOUND; ./finish_fd.sh "$X" ${R}_cur.sol "$FS" ${R}_fin | tail -n 1; break; fi
  for pr in $bad; do p=${pr%%(*}; a=${p%%-*}; b=${p##*-}; k=$(echo $a | cut -c1 | tr PL pl); HP="$HP; $k ${a:1} ${b:1}"; done
  echo "hard pairs now: $HP"
done
