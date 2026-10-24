#!/bin/bash
# usage: r3/score348.sh BASE GROUP VOLT  -> best cost over the 348 labelled (4,3) singular sets (and which), at fixed voltages
W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w
best=999; bf=""
for f in r3/flags43/s*.flags; do c=$(VOLT=$3 $W/ctrl_search $1 $2 $f 1 1 | sed 's/.*cost=\([0-9]*\).*/\1/'); if [ "$c" -lt "$best" ]; then best=$c; bf=$f; fi; done
echo "$best $bf"
