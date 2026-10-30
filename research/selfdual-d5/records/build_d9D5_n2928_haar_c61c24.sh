#!/bin/bash
# Rebuild and check d9D5_n2928_haar_c61c24 (run from research/selfdual-d5/).  (9,5), 2,928 vertices: G = C61 : C24 = SmallGroup(1464,1), y acts with order 6; found by sdtabu K = 9 (record 6, type (3,3)).
# Haar graph of G = <x, y | x^61 = y^24 = 1, y x y^-1 = x^14>, elements x^i y^j written (i,j), S = {0,0 19,0 42,12 59,4 35,20 54,7 30,5 57,14 56,10}, (g,A) ~ (s g, B).
# Self-dual: psi(g) = beta(g)^-1 with beta(x) = x^60, beta(y) = x^0 y^13 maps S to itself, so the graph is also a Cayley
# graph of G : <tau> (tau g tau = beta(g)) with T = S tau.
S="0,0 19,0 42,12 59,4 35,20 54,7 30,5 57,14 56,10"
python3 records/build_metacyclic_haar.py 61 24 14 "$S" /tmp/d9D5_n2928_haar_c61c24.edges 5        # GAP-free build + BFS from every vertex
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n2928_haar_c61c24.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n2928_haar_c61c24.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n2928_haar_c61c24.edges 9 5
cmp /tmp/d9D5_n2928_haar_c61c24.edges records/d9D5_n2928_haar_c61c24.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n2928_haar_c61c24.edges     # b018047dc73e01113857ca8eb258da2d6ae3f7e693dd64f08466dead75ecd233
python3 records/find_beta_meta.py 61 24 14 "$S"                                    # includes: 60 0 13
python3 records/build_metacyclic_cayley.py 61 24 14 60 0 13 "$S" /tmp/d9D5_n2928_haar_c61c24_cayley.edges 5
python3 src/canon_eq.py records/d9D5_n2928_haar_c61c24.edges /tmp/d9D5_n2928_haar_c61c24_cayley.edges
