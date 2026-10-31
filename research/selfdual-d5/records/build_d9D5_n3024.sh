#!/bin/bash
# Rebuild and check the (9,5) graph on 3,024 vertices (run from research/selfdual-d5/).
# Haar graph of G = C7 : (C3 x ((C3 x C3) : C8)) = SmallGroup(1512,783); formulas, S and the self-dual automorphism in
# records/build_d9D5_n3024.py.
python3 records/build_d9D5_n3024.py /tmp/d9D5_n3024.edges /tmp/d9D5_n3024_cayley.edges   # formula build + BFS from every vertex; Cayley build
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n3024.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n3024.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n3024.edges 9 5
cmp /tmp/d9D5_n3024.edges records/d9D5_n3024_haar_c7_c3xc3sqc8.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n3024_haar_c7_c3xc3sqc8.edges   # 150a0027094cd3bc1448c8ac5b6e3097d6e978f677884a3c3285e742a05fbbda
/tmp/apsp /tmp/d9D5_n3024_cayley.edges 9 5 | tail -1
python3 src/canon_eq.py records/d9D5_n3024_haar_c7_c3xc3sqc8.edges /tmp/d9D5_n3024_cayley.edges
# The search: gap -q -c 'N:=1512;; ID:=783;; OUT:="/tmp/g1512_783.ht";; NOEXT:=1;;' src/export_sd.g
#   K=9 SECS=2 DEEP=10,25 TYPES=1,3,5 src/sdtabu /tmp/g1512_783.ht all   (record 5, type (3,3), in the sweep's DEEP
#   phase; records/d9D5_n3024_haar_c7_c3xc3sqc8_search.out).  Coordinates: x^i z^c w1^a w2^b u^k for explicit
#   generators in GAP, checked on all 1512^2 products.
