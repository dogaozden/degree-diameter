#!/bin/bash
# do_cell.sh NAME BASEFILE n j POINT SEED: polygon cover of a generalized n-gon (n=4 quadrangle, n=6 hexagon) with j
# matchings over Z_{2j+1}, plus one unit per matching at POINT. Writes cells/NAME.{state,units,edges,apsp.txt}.
NAME=$1; BASE=$2; N=$3; J=$4; PT=$5; SEED=${6:-1}
D=$((N+1)); Q=$(head -1 $BASE | cut -d' ' -f2); DEG=$((Q+1+J))
US=""; for t in $(seq 1 $J); do US="$US $PT:$t"; done
python3 mkunits.py --n $N $BASE $J $SEED cells/$NAME.state cells/$NAME.units $US 2> cells/$NAME.mk.log || { cat cells/$NAME.mk.log; exit 1; }
python3 unit_edges.py $BASE cells/$NAME.state cells/$NAME.units cells/$NAME.edges > cells/$NAME.edges.info
sha256sum cells/$NAME.edges | cut -c1-64 > cells/$NAME.edges.sha256
echo "$NAME: $(cat cells/$NAME.edges.info) d=$DEG D=$D"
