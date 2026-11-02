#!/bin/bash
# chain3.sh: same as chain2 with a new priority order (168 groups and order-42 groups first), 300-set cap.
cd /home/user/degree-diameter/research/squads/deep-37
W=squad/r1/c1
while pgrep -f "drive.py 3e7 squad/r1/c1/gs/n168/g14_1" >/dev/null; do sleep 5; done
run_group() { # ORDER ID MAXSETS(number or probe)
  local D=$W/gs/n168/g$1_$2
  if [ "$3" = "probe" ]; then timeout 300 nice -n 15 bash $W/gen37.sh $1 $2 168 probe
  elif [ ! -f $D/est.txt ]; then timeout 400 nice -n 15 bash $W/gen37.sh $1 $2 168 $3; fi
  if [ -f $D/est.txt ]; then nice -n 15 python3 $W/drive.py 3e7 $D/est.txt; fi
  echo "$(date -u +%T) group $1 $2 done (cap $3)" >> $W/logs/chain.log
}
run_group 168 42 probe
run_group 168 43 300
for i in 1 2 3 4 5 6; do run_group 42 $i 300; done
echo "$(date -u +%T) PHASE1 done" >> $W/logs/chain.log
for i in 2; do run_group 14 $i 300; done
for i in 1 2 3 4; do run_group 28 $i 300; done
for i in $(seq 1 13); do run_group 56 $i 300; done
echo "$(date -u +%T) PHASE2 done" >> $W/logs/chain.log
for i in $(seq 1 15); do run_group 84 $i 300; done
echo "$(date -u +%T) PHASE3 done" >> $W/logs/chain.log
