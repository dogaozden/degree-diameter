#!/bin/bash
# head-to-head: random-S annealing (haar_fast) vs k=3 orbit annealing (haar_sym), same groups, seeds, budget
cd /tmp/claude-0/-home-user-degree-diameter/3eceb95b-8ad3-596d-91d8-944ec5b540f8/scratchpad/cmp
SECS=$1; shift
while read -r spec d D grp; do
  [ -z "$d" ] && continue
  spec=${spec//,/ }
  for s in 1 2 3 4; do
    r=$(timeout $((SECS+30)) ../hf $d $D $SECS $s 8 /dev/null $grp 2>/dev/null | grep RESULT)
    echo "random  $d $D $grp seed $s :: $r"
    o=$(ORBIT="$spec" timeout $((SECS+30)) ../hs $d $D $SECS $s 8 /dev/null $grp 2>/dev/null | grep RESULT)
    echo "orbit$spec $d $D $grp seed $s :: $o"
  done
done
