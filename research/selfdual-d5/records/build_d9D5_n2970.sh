#!/bin/bash
# Rebuild and check the (9,5) graph on 2,970 vertices (run from research/selfdual-d5/).
# Haar graph of G = Heis(3) x (C11 : C5) = SmallGroup(1485,4); formulas, S and the self-dual automorphism in
# records/build_d9D5_n2970.py.
# 1) GAP-free build from the formula + BFS from every vertex, and the Cayley description over G : <tau>:
python3 records/build_d9D5_n2970.py /tmp/d9D5_n2970.edges /tmp/d9D5_n2970_cayley.edges
# 2) all-pairs checks (apsp.c at D = 5 and D = 4) and the independent Python checker:
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n2970.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n2970.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n2970.edges 9 5
cmp /tmp/d9D5_n2970.edges records/d9D5_n2970_haar_heis3_f55.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n2970_haar_heis3_f55.edges   # d51d229ebb737ce955e642776d453413393bca46bea4549e53f3f631821b8827
/tmp/apsp /tmp/d9D5_n2970_cayley.edges 9 5 | tail -1
python3 src/canon_eq.py records/d9D5_n2970_haar_heis3_f55.edges /tmp/d9D5_n2970_cayley.edges
# 3) the search: gap -q -c 'N:=1485;; ID:=4;; OUT:="/tmp/g1485_4.ht";; NOEXT:=1;;' src/export_sd.g
#    K=9 SECS=300 SEED=11 src/sdtabu /tmp/g1485_4.ht 5 3 3     (record 5, type (3,3); found after 297 s;
#    records/d9D5_n2970_haar_heis3_f55_search.out).  Coordinates of the export's elements: an explicit isomorphism
#    onto the formula group (GAP IsomorphismGroups), checked on all 1485^2 products.
