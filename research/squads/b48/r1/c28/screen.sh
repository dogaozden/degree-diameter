#!/bin/bash
cd /home/user/degree-diameter/research/squads/b48/r1/c28
while read m k r; do
  THREADS=1 timeout 120 nice -n 10 ./cay $m $k $r 1 1 2>&1 | grep -E "GROUP|RESULT" | tr '\n' ' '; echo
done < screen_list.txt > screen_out.txt
