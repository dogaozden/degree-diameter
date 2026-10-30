#!/bin/bash
# stop_driver.sh run1|run_tabu: stop a sweep driver (sweep.sh / sweep_tabu.sh and its xargs); groups already running finish.
w=$1; s=$([ "$w" = run_tabu ] && echo sweep_tabu || echo sweep)
pgrep -f "^/bin/bash src/$s.sh " | xargs -r kill; pgrep -f "^xargs -P [0-9]+ -n 2 src/$w.sh" | xargs -r kill
sleep 1; echo "in flight:"; pgrep -af "^/bin/bash src/$w.sh " | awk '{print $(NF-1)"_"$NF}'
