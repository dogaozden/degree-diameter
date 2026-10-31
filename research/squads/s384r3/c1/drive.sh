#!/bin/bash
# resumable driver: one SmallGroup per sweep.sh call, done list in logs/done.txt; outer timeout stops it
cd /home/user/degree-diameter/research/squads/s384r3/c1
export PATH=/tmp/claude-0/bin:$PATH
for spec in 722:5 724:5 726:13 728:40 730:4 732:18 734:2 736:195; do
  o=${spec%:*}; n=${spec#*:}
  for id in $(seq 1 $n); do
    grep -qx "$o $id" logs/done.txt 2>/dev/null && continue
    echo "START $o $id $(date +%T)" >> logs/progress.txt
    timeout 900 ./sweep.sh $o 2 6 3 "[$id]" 1
    echo "$o $id" >> logs/done.txt
  done
done
echo "ALLDONE $(date +%T)" >> logs/progress.txt
