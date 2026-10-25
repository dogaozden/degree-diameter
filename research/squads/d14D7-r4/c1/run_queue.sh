#!/bin/bash
# c1 (r4): sequential orbitclique queue (60 s CPU, seed 1, heavy.sh 150). Detached so it survives the tool call.
C=/home/user/degree-diameter/research/squads/d14D7-r4/c1
HEAVY=/home/user/degree-diameter/research/squads/bin/heavy.sh
MAP=/home/user/degree-diameter/research/cell147/data/E11.map
ORB=/home/user/degree-diameter/research/cell147/units/orbitclique
cd $C
# wait (at most ~2 min) for the H20_4 job that was orphaned when the first batch shell died
for i in $(seq 1 60); do grep -q '^best' $C/log_s1_d10_0__s1_d4_0__H20_4.txt 2>/dev/null && break; sleep 2; done
echo "H20_4 $(grep '^best' $C/log_s1_d10_0__s1_d4_0__H20_4.txt)" >> $C/queue.out
run() {  # run TAG PERMFILE
  $HEAVY 150 $ORB $MAP "$2" 60 1 $C/flags_$1.txt 2> $C/log_$1.txt
  echo "$1 rc=$? $(grep '^best' $C/log_$1.txt)" >> $C/queue.out
}
run s2_d10_0__s2_d4_0__H20_29 $C/permH_s2_d10_0__s2_d4_0__H20_29.txt
run s2_d10_1__s2_d4_1__H20_34 $C/permH_s2_d10_1__s2_d4_1__H20_34.txt
run s1_d10_0__s1_d8_0__H8_8 $C/permH_s1_d10_0__s1_d8_0__H8_8.txt
run s1_d10_0__s1_d4_0__H10_3 $C/permH_s1_d10_0__s1_d4_0__H10_3.txt
run native_s2d8 /home/user/degree-diameter/research/cell147/data/perms_q11/elems_o4_s2_d8_0.txt
echo QUEUE_DONE >> $C/queue.out
