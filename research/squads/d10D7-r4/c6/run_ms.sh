#!/bin/bash
# wait for the section batch to finish, then multi-start the full points search (one process at a time)
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
while ! grep -q DONE sec_summary.txt 2>/dev/null; do sleep 2; done
: > ms_summary.txt
for s in $(seq 40 79); do
  timeout 30 nice -n 10 ./ls6c $H points 3 $s MS_s$s - - > MS_s$s.log 2>&1
  echo "seed $s : $(grep FOUND MS_s$s.log | tail -1)" >> ms_summary.txt
done
timeout 100 nice -n 10 ./ls6c $H points 60 11 MS_from72 points72.txt - > MS_from72.log 2>&1
echo "from72 : $(grep FOUND MS_from72.log | tail -1) | $(tail -1 MS_from72.log)" >> ms_summary.txt
echo DONE >> ms_summary.txt
