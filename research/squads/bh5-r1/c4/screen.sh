#!/bin/bash
# Round-1 screen: short vl INC=1 runs, one process at a time. Output: $C/logs/screen.txt
C=/home/user/degree-diameter/research/squads/bh5-r1/c4
V=/home/user/degree-diameter/research/beyond-haar-d5/vl
cd /home/user/degree-diameter/research/beyond-haar-d5
run() { # label base group secs
  label=$1; base=$2; grp=$3; secs=$4
  out=$(timeout $((secs+60)) nice -n 10 env INC=1 D=5 SECS=$secs SEED=${SEED:-1} OUT=$C/sols/$label.sol $V $base $grp 2>$C/logs/$label.err | tail -1)
  echo "$label $out" | tee -a $C/logs/screen.txt
}
run w4z7_plain  $C/bases/w4_j2_s1.txt  $C/groups/sg_7_1.txt 25
run w4z7_double $C/bases/w4_j2d_s1.txt $C/groups/sg_7_1.txt 25
for i in 1 2 3 4 5; do run w4o8_plain_$i $C/bases/w4_j2_s1.txt $C/groups/sg_8_$i.txt 12; done
run w5z4_j1   $C/bases/w5_j1_s1.txt $C/groups/sg_4_1.txt 25
run w5v4_j1   $C/bases/w5_j1_s1.txt $C/groups/sg_4_2.txt 25
run w3z15_j3  $C/bases/w3_j3_s1.txt $C/groups/sg_15_1.txt 25
for i in $(seq 1 14); do run w3o16_j3_$i $C/bases/w3_j3_s1.txt $C/groups/sg_16_$i.txt 8; done
echo DONE >> $C/logs/screen.txt
