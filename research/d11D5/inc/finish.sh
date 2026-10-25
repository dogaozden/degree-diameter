#!/bin/bash
# finish.sh base.in nu_file out_prefix d D : DM voltages (flags 3*nu, jump copies 1 and 4) -> exact Z6 lift cost (z6lift),
# explicit edge list, all-pairs BFS check (apsp.c).  Needs /tmp/z6 (z6lift.c) and /tmp/apsp (lifts/coordinator_check/apsp.c).
set -e
base=$1; nu=$2; out=$3; d=$4; D=$5
n=$(head -1 $base | cut -d' ' -f1)
python3 -c "
import sys
nu=open('$nu').read().split()
with open('$out.volt','w') as g:
    for v in nu: g.write(f'{3*int(v)}\n')
    for p in range($n): g.write('1\n4\n')
"
SCORE=1 VOLT=$out.volt EDGES=$out.edges /tmp/z6 $base
/tmp/apsp $out.edges $d $D | tail -2
sha256sum $out.edges
