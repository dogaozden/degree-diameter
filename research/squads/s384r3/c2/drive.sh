#!/bin/bash
# c2 driver: sweep.sh over orders in chunks of 10 groups; no new chunk starts after 1800 s; each chunk under timeout 900
cd /home/user/degree-diameter/research/squads/s384r3/c2
export PATH=/tmp/claude-0/bin:$PATH
T0=$(date +%s); echo "START $(date +%T)" >> logs/progress.txt
for spec in 738:10 740:15 742:4 744:54 746:2 748:11 750:39 752:42 754:4 758:2 760:39 762:6 764:4 766:2 756:189; do
  o=${spec%:*}; n=${spec#*:}
  for a in $(seq 1 10 $n); do
    b=$((a+9)); [ $b -gt $n ] && b=$n
    if [ $(( $(date +%s) - T0 )) -ge 1800 ]; then echo "STOP before $o [$a..$b] $(date +%T)" >> logs/progress.txt; break 2; fi
    timeout 900 ./sweep.sh $o 2 6 3 "[$a..$b]" 1 > logs/chunk_${o}_${a}.out 2>&1
    echo "DONE rc=$? $o [$a..$b] $(date +%T)" >> logs/progress.txt
  done
done
echo "END $(date +%T)" >> logs/progress.txt
