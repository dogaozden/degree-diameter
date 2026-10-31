#!/bin/bash
# Rebuild and check the (9,5) graph on 2,976 vertices (run from research/selfdual-d5/).
# Haar graph of G = C31 : (C3 x Q16) = SmallGroup(1488,11); formulas, S and the self-dual automorphism in
# records/build_d9D5_n2976.py.
python3 records/build_d9D5_n2976.py /tmp/d9D5_n2976.edges /tmp/d9D5_n2976_cayley.edges   # formula build + BFS from every vertex; Cayley build
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n2976.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n2976.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n2976.edges 9 5
cmp /tmp/d9D5_n2976.edges records/d9D5_n2976_haar_c31_c3q16.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n2976_haar_c31_c3q16.edges   # a124e06804fc9bd58db1c54a45f2853dd15f3f17b4a524617388a906aa3b5415
/tmp/apsp /tmp/d9D5_n2976_cayley.edges 9 5 | tail -1
python3 src/canon_eq.py records/d9D5_n2976_haar_c31_c3q16.edges /tmp/d9D5_n2976_cayley.edges
# The search: gap -q -c 'N:=1488;; ID:=11;; OUT:="/tmp/g1488_11.ht";; NOEXT:=1;;' src/export_sd.g
#   K=9 SECS=300 SEED=11 src/sdtabu /tmp/g1488_11.ht 11 3 3   (record 11, type (3,3); records/d9D5_n2976_haar_c31_c3q16_search.out;
#   the seed-23 run found an isomorphic graph, and the sweep's own pass found sets in record 10, logs/K9/tabu/1488_11.out).
#   Coordinates of the export's elements: x^i z^c a^k b^l for explicit generators in GAP, checked on all 1488^2 products.
