#!/bin/bash
# usage: analyse.sh PREFIX N   (PREFIX.edges = controller "a b e", PREFIX.echart = per-edge chart, PREFIX.log = annealer log)
# prints: annealer best_cost, exact checker (pair_cost, uncovered ordered pairs, diameter), and for an independent
# cross-check: apsp verdict and bfs_all sum of even distances >= 6 (same-side pairs at distance > 4) on the elift lift.
D=/home/user/degree-diameter/research/squads/d12D5-r1/c8; R=/home/user/degree-diameter/research/d12D5
P=$1; N=$2
echo "== $P"
grep -o "best_cost=[0-9]*" $P.log 2>/dev/null
DETAIL=1 $D/exact_cover $P.edges $P.echart $N > $P.exact.txt 2>&1
grep -E "^lift|^uncovered|^pair_cost|^VERDICT" $P.exact.txt
echo "flags (side block fibre z_count uncovered_points):"; grep "flag" $P.exact.txt | sed 's/  flag //' | head -12
python3 $R/elift.py $P.edges $P.echart $P.lift.edges > /dev/null
echo "apsp: $(timeout 250 nice -n 10 $R/apsp $P.lift.edges 12 5 | tail -1)"
timeout 280 nice -n 10 $R/bfs_all $P.lift.edges > $P.bfs.txt
awk '/dist/ {d=$2; sub(":","",d); if (d+0>=6 && (d+0)%2==0) s+=$3} /max_ecc/ {print "bfs_all: " $0} END {print "bfs_all same-side pairs at dist>=6 (even): " s+0}' $P.bfs.txt
rm -f $P.lift.edges
