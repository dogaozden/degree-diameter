#!/bin/bash
# Rebuild and check d9D5_n2934_haar_c163c9 (run from research/selfdual-d5/).  (9,5), 2,934 vertices: G = C163 : C9 = SmallGroup(1467,1), y acts with order 3; found by sdtabu K = 9 (record 1, type (3,3)) in a 300 s deep run (seed 11).
# Haar graph of G = <x, y | x^163 = y^9 = 1, y x y^-1 = x^58>, elements x^i y^j written (i,j), S = {0,0 4,0 105,0 143,4 39,5 119,8 56,1 117,7 106,2}, (g,A) ~ (s g, B).
# Self-dual: psi(g) = beta(g)^-1 with beta(x) = x^162, beta(y) = x^0 y^1 maps S to itself, so the graph is also a Cayley
# graph of G : <tau> (tau g tau = beta(g)) with T = S tau.
S="0,0 4,0 105,0 143,4 39,5 119,8 56,1 117,7 106,2"
python3 records/build_metacyclic_haar.py 163 9 58 "$S" /tmp/d9D5_n2934_haar_c163c9.edges 5        # GAP-free build + BFS from every vertex
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n2934_haar_c163c9.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n2934_haar_c163c9.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n2934_haar_c163c9.edges 9 5
cmp /tmp/d9D5_n2934_haar_c163c9.edges records/d9D5_n2934_haar_c163c9.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n2934_haar_c163c9.edges     # f5e6c338c0068e874e3e0f472ac4be620a4391f53488604bedfe8c7cb2c6af18
python3 records/find_beta_meta.py 163 9 58 "$S"                                    # includes: 162 0 1
python3 records/build_metacyclic_cayley.py 163 9 58 162 0 1 "$S" /tmp/d9D5_n2934_haar_c163c9_cayley.edges 5
python3 src/canon_eq.py records/d9D5_n2934_haar_c163c9.edges /tmp/d9D5_n2934_haar_c163c9_cayley.edges
