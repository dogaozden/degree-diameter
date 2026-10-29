#!/bin/bash
# Rebuild and check the (5,5) graph on 360 vertices: lift of the base [[2,3],[3,2]] by SmallGroup(90,6) = C15 x S3.
# Run from research/beyond-haar-d5. The table records/g90_6_C15xS3.table is GAP's Elements(SmallGroup(90,6)) with the
# identity moved first (src/gap_tab_aut.g); with GAP: gap -q -c 'ORDER:=90; ID:=6; OUT:="t";' src/gap_tab_aut.g
set -e
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
python3 exh/b4a2x_edges.py records/g90_6_C15xS3.table "SOL x 6 y 5 34 z 1 31 68 w 6" /tmp/n360.edges
cmp /tmp/n360.edges records/d5D5_n360_lift_g90_6.edges && echo "edge list identical"
/tmp/apsp /tmp/n360.edges 5 5; /tmp/apsp /tmp/n360.edges 5 4 | tail -1
python3 records/check_independent.py /tmp/n360.edges 5 5
