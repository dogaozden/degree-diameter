#!/bin/bash
# usage: runlist.sh LISTFILE START END  (lines START..END of LIST: LABEL|EXPR|H); prints only groups with an export
C3=/home/user/degree-diameter/research/squads/handsoff-65/c3
sed -n "$2,$3p" $1 | while IFS='|' read -r lab expr h; do
  out=$(PRE="$PRE" $C3/runone.sh "$lab" "$expr" "$h" ${MS:-300000} 2>/dev/null)
  if echo "$out" | grep -q "RESULT"; then
    best=$(echo "$out" | grep RESULT | sed 's/.*best \([0-9]*\) vertices \([0-9]*\).*/\1 \2/' | sort -n | head -1)
    sol=$(echo "$out" | grep RESULT | grep -c "solutions [1-9]")
    echo "$lab h=$h best/n=$best sols=$sol"
  fi
done
