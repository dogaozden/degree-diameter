#!/bin/bash
# Verify a cost-0 controller from mlift_chart run with charts/pat_u8_qXX.txt:
# relabel controller colour c -> chart letter p[c] (p = permutation qXX in charts/perm_list_u8.txt),
# build the route-chart lift with charts/chart_u8.txt and run the all-pairs check.
# usage: verify_ctrl.sh CONTROLLER.edges qXX OUTDIR
set -e
D=$(cd "$(dirname "$0")" && pwd); C=$1; Q=$2; O=$3; mkdir -p "$O"
P=$(grep "^$Q " "$D/charts/perm_list_u8.txt" | sed 's/^[^(]*(//; s/).*//; s/,//g')
awk -v p="$P" 'BEGIN{split(p,q," ")} {print $1, $2, q[$3+1]}' "$C" > "$O/ctrl_relabelled.edges"
python3 "$D/build_lift_general.py" "$O/ctrl_relabelled.edges" "$D/charts/chart_u8.txt" "$O/lift.edges"
[ -x /tmp/claude-0/apsp ] || gcc -O3 -o /tmp/claude-0/apsp "$D/../../lifts/coordinator_check/apsp.c"
/tmp/claude-0/apsp "$O/lift.edges" 16 5
