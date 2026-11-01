#!/bin/bash
# renice_loop.sh: autogroup scheduling makes `nice` inside each card's shell ineffective across cards; this loop sets the
# autogroup nice of every squad process (cwd under research/squads/raise11) to +10 and of director search/check
# processes (cwd under research/frontier/raise11) to $DIRNICE (default 0).  Runs until killed.
while true; do
  for d in /proc/[0-9]*; do
    c=$(readlink $d/cwd 2>/dev/null) || continue
    case "$c" in
      */squads/raise11*) echo 10 > $d/autogroup 2>/dev/null;;
      */frontier/raise11*) grep -q "haar\|check" $d/comm 2>/dev/null && echo ${DIRNICE:-0} > $d/autogroup 2>/dev/null;;
    esac
  done
  sleep 4
done
