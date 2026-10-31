#!/bin/bash
# per-order closed/total for the queue, plus VALID count
cd /home/user/degree-diameter/research/squads/handsoff-65/c19
awk '{print $1}' queue.txt | sort -n | uniq -c | while read tot ord; do
  cl=0; for id in $(awk -v o=$ord '$1==o{print $2}' queue.txt); do grep -q '^DONE' logs/${ord}_${id}.out 2>/dev/null && cl=$((cl+1)); done
  echo -n "$ord:$cl/$tot "
done; echo
echo "VALID lines: $(cat logs/*.out 2>/dev/null | grep -c '^VALID')  ASIDE lines: $(cat logs/*.out 2>/dev/null | grep -c '^ASIDE')  NOEXPORT: $(grep -l NOEXPORT logs/*.out 2>/dev/null | wc -l)"
