#!/bin/bash
# c1 (r4): second queue, starts after run_queue.sh has written QUEUE_DONE.
C=/home/user/degree-diameter/research/squads/d14D7-r4/c1
HEAVY=/home/user/degree-diameter/research/squads/bin/heavy.sh
MAP=/home/user/degree-diameter/research/cell147/data/E11.map
ORB=/home/user/degree-diameter/research/cell147/units/orbitclique
cd $C
for i in $(seq 1 300); do grep -q QUEUE_DONE $C/queue.out 2>/dev/null && break; sleep 2; done
run() {
  $HEAVY 150 $ORB $MAP "$2" 60 1 $C/flags_$1.txt 2> $C/log_$1.txt
  echo "$1 rc=$? $(grep '^best' $C/log_$1.txt)" >> $C/queue.out
}
run s2_d10_1__s2_d4_1__H10_33 $C/permH_s2_d10_1__s2_d4_1__H10_33.txt
run native_s1d10_1 /home/user/degree-diameter/research/cell147/data/perms_q11/elems_o4_s1_d10_1.txt
echo QUEUE2_DONE >> $C/queue.out
