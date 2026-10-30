#!/bin/bash
# sequential sweeps for card c6 (|H| = 2, SKIPHAAR); orders 722-738 with 2*odd order are empty (see report)
cd /home/user/degree-diameter/research/squads/s65r6/c6
for o in 724 740 732 728; do
  echo "START $o $(date +%T)" >> logs/driver.log
  ./sweep.sh $o 2 6 2 "[1..$(python3 -c "print({724:5,740:15,732:18,728:40}[$o])")]"
  echo "END $o $(date +%T)" >> logs/driver.log
done
for a in 1 41 81 121 161; do
  b=$((a+39)); [ $b -gt 195 ] && b=195
  echo "START 736 [$a..$b] $(date +%T)" >> logs/driver.log
  ./sweep.sh 736 2 6 2 "[$a..$b]"
  echo "END 736 [$a..$b] $(date +%T)" >> logs/driver.log
done
echo "ALLDONE $(date +%T)" >> logs/driver.log
