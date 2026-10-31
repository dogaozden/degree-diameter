#!/bin/bash
# Rebuild and check the (9,5) graph on 3,000 vertices (run from research/selfdual-d5/).
# Haar graph of G = (C5 x C5 x C5) : (C3 : C4) = SmallGroup(1500,113); formulas, S and the self-dual automorphism in
# records/build_d9D5_n3000.py.
python3 records/build_d9D5_n3000.py /tmp/d9D5_n3000.edges /tmp/d9D5_n3000_cayley.edges   # formula build + BFS from every vertex; Cayley build
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n3000.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n3000.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n3000.edges 9 5
cmp /tmp/d9D5_n3000.edges records/d9D5_n3000_haar_c5cube_dic3.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n3000_haar_c5cube_dic3.edges   # afec2757d72b73a694fad479306c6f7f762e44a39851241afc204883348f43ca
/tmp/apsp /tmp/d9D5_n3000_cayley.edges 9 5 | tail -1
python3 src/canon_eq.py records/d9D5_n3000_haar_c5cube_dic3.edges /tmp/d9D5_n3000_cayley.edges
# The search: gap -q -c 'N:=1500;; ID:=113;; OUT:="/tmp/g1500_113.ht";; NOEXT:=1;;' src/export_sd.g
#   K=9 SECS=300 SEED=23 STALL=2000 src/sdtabu /tmp/g1500_113.ht 5 5 2   (record 5, type (5,2), found after 204 s;
#   records/d9D5_n3000_haar_c5cube_dic3_search.out).  Coordinates of the export's elements: v s^i u^j for explicit
#   generators in GAP (basis of the normal Sylow 5-subgroup, s and u in a Hall {2,3}-subgroup), checked on all 1500^2 products.
