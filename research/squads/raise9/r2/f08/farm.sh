#!/bin/bash
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r2/f08
while pgrep -f "screen7.sh" >/dev/null; do sleep 2; done
for s in 101 102 103; do
  THREADS=1 SAVEBEST=b_f08_7_$s.txt timeout 105 nice -n 10 $B/haar_gen3s 7 9 90 $s 8 OUT_f08_79_$s.txt prod meta 19 3 7 meta 239 17 6 1 > log79_$s.txt 2>&1
done
for s in 201 202 203; do
  THREADS=1 SAVEBEST=b_f08_6_$s.txt timeout 105 nice -n 10 $B/haar_gen3s 6 9 90 $s 8 OUT_f08_69_$s.txt prod meta 13 3 3 meta 239 7 10 1 > log69_$s.txt 2>&1
done
echo FARMDONE > farm.done
