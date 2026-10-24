#!/bin/bash
# usage: r3/run348.sh BASE GROUP SETIDX SECONDS TAG
W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w
f=r3/flags43/s$3.flags
timeout $(($4 + 20)) nice -n 5 $W/ctrl_search $1 $2 $f $4 1 r3/runs_348/$5_s$3 > r3/runs_348/$5_s$3.out 2>&1
echo "$5 s$3 $(tail -n 1 r3/runs_348/$5_s$3.out | sed 's/.*best_cost=\([0-9]*\).*/cost=\1/')"
