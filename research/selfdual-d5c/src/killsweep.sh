#!/bin/bash
# killsweep.sh: stop all drivers and searches. Scripts run through their shebang carry their own process names
# (sweep.sh, run1.sh, probes.sh), so match names exactly (pkill -x); fsd runs under timeout/nice wrappers.
pkill -x sweep.sh; pkill -x probes.sh; pkill -x run1.sh
for t in $(ps -eo pid,args | awk '$2=="timeout" && /src\/fsd/ {print $1}'); do kill $t; done
pkill -x fsd
