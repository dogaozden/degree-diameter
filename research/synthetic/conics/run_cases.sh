#!/bin/bash
# usage: run_cases.sh q k E ADD timeout outfile   (runs every orbit case of sat_polar.py, 3 in parallel)
PY=/tmp/claude-0/-home-user-degree-diameter/db23ed3e-5ef1-51fa-9a71-0fdc3180aa1f/scratchpad/venv/bin/python
q=$1; k=$2; E=$3; ADD=$4; T=$5; OUT=$6
cases="A:1"
for t in con ext int; do for r in $(seq $((q+1)) -1 2); do cases="$cases $t:$r"; done; done
echo $cases | tr ' ' '\n' | xargs -P ${PAR:-3} -I{} sh -c "timeout $T nice -n 5 $PY sat_polar.py $q $k --E $E --ADD $ADD --case {} --time $T 2>&1 | tr '\n' ' ' ; echo" >> $OUT
