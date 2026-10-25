#!/bin/bash
# squad c2, queue 2: waits for queue 1 to finish, then flags every finished chart and runs the powers-of-M structured search (200 s).
C=/home/user/degree-diameter/research/squads/r2-chartlift/c2
while pgrep -x queue1.sh >/dev/null; do sleep 5; done
echo "QUEUE1_ENDED $(date +%T)" >> $C/runs/summary.txt
$C/check_runs.sh $C/runs/a_*.txt $C/runs/b_*.txt > $C/runs/flags_queue1.txt 2>&1
echo "FLAGS_DONE $(date +%T)" >> $C/runs/flags_queue1.txt
cd /home/user/degree-diameter/research/squads/r2-chartlift/c2 && timeout 900 nice -n 10 python3 powers_search.py 200 1 $C/powers > $C/powers/search_s1.log 2>&1
echo "POWERS_DONE $(date +%T)" >> $C/powers/search_s1.log
