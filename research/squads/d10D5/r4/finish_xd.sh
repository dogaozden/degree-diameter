#!/bin/bash
# finish_xd.sh STATE.sol C0.lift2.sol "FDSET" "x:L ..." OUT: exact check of a state with FLAGDEL flags FDSET and
# ordinary deleted flag edges (x:L, each with one hub per fibre): build_fd.py graph, then edgedel.py per deleted edge,
# then apsp and the list of failing pairs (failpairs.py).
X=$1; C=$2; FS=$3; XD=$4; O=$5
./finish_fd.sh "$X" "$C" "$FS" $O > /dev/null 2>&1
cp $O.fd.edges $O.x.edges
for t in $XD; do x=${t%%:*}; L=${t##*:}; python3 edgedel.py $O.x.edges "$X" "$C" $x $L $O.x2.edges > /dev/null && mv $O.x2.edges $O.x.edges; done
./apsp $O.x.edges 10 5 | tail -n 2
python3 failpairs.py $O.x.edges | wc -l
