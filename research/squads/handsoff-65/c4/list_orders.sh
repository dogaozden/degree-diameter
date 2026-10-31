#!/bin/bash
# usage: list_orders.sh LO HI STEP  -> prints "ORDER COUNT" for orders LO..HI (step STEP) that the SmallGroups library has
for n in $(seq $1 $3 $2); do
  c=$(timeout 60 gap -q -c "Print(NumberSmallGroups($n), \"\n\"); QUIT;" </dev/null 2>/dev/null | head -1)
  case "$c" in ''|*[!0-9]*) ;; *) echo "$n $c";; esac
done
