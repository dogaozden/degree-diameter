#!/bin/bash
# usage: verify.sh OUT_EDGES PX CHART_FILE WORKDIR   (OUT_EDGES lines "a b colour"; PX e.g. p1; CHART_FILE e.g. chart_p4.txt)
set -e
EDGES=$1; PX=$2; CHART=$3; OD=$4; SQ=/home/user/degree-diameter/research/theorems/squad165
mkdir -p "$OD"
PERM=$(grep "^$PX " $SQ/charts/perm_list.txt | sed 's/.*(\(.*\))/\1/' | tr -d ' ')
awk -v P="$PERM" 'BEGIN{ n=split(P,p,","); } { print $1, $2, p[$3+1] }' "$EDGES" > "$OD/relabelled.edges"
cd $SQ && python3 build_lift_general.py "$OD/relabelled.edges" "charts/$CHART" "$OD/lift.edges"
/tmp/claude-0/r2c3/apsp "$OD/lift.edges" 16 5
