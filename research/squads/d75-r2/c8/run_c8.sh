#!/bin/bash
# run_c8.sh LABEL "GAP_ASSIGN_EXPR": export G (bound by the expression) and run haar75 anti; summary in logs/summary.txt
D=/home/user/degree-diameter/research/squads/d75-r2/c8
R=/home/user/degree-diameter/research/d75-raise
L=$1; EXPR=$2
mkdir -p $D/tmp $D/logs
export TMPDIR=$D/tmp
F=$D/tmp/$L.ht
t0=$(date +%s)
timeout 600 nice -n 15 gap -q -c "$EXPR;; OUT:=\"$F\";;" $R/src/export.g < /dev/null > $D/tmp/$L.gap.log 2>&1
if [ ! -s $F ]; then echo "$L GAPFAIL" >> $D/logs/summary.txt; exit 0; fi
MAXEV=100000000 MAXEVF=3000000 EDGES=$D/$L.edges timeout 900 nice -n 15 $R/src/haar75 $F anti > $D/logs/$L.out 2>&1
rc=$?
sols=$(grep -c "^SOL" $D/logs/$L.out)
echo "$L rc $rc sols $sols secs $(( $(date +%s) - t0 ))" >> $D/logs/summary.txt
rm -f $F
