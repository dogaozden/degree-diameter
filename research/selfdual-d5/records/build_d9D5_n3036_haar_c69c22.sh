#!/bin/bash
# Rebuild and check d9D5_n3036_haar_c69c22 (run from research/selfdual-d5/).  (9,5), 3,036 vertices: G = C69 : C22 = S3 x (C23 : C11) = SmallGroup(1518,2); found by a 300 s deep sdtabu run (record 2, type (3,3), seed 11, STALL 2000).
# Haar graph of G = <x, y | x^69 = y^22 = 1, y x y^-1 = x^8>, elements x^i y^j written (i,j), S = {0,0 66,11 56,11 28,13 22,9 13,15 64,7 25,14 8,8}, (g,A) ~ (s g, B).
# Self-dual: psi(g) = beta(g)^-1 with beta(x) = x^22, beta(y) = x^0 y^1 maps S to itself, so the graph is also a Cayley
# graph of G : <tau> (tau g tau = beta(g)) with T = S tau.
S="0,0 66,11 56,11 28,13 22,9 13,15 64,7 25,14 8,8"
python3 records/build_metacyclic_haar.py 69 22 8 "$S" /tmp/d9D5_n3036_haar_c69c22.edges 5        # GAP-free build + BFS from every vertex
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n3036_haar_c69c22.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n3036_haar_c69c22.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n3036_haar_c69c22.edges 9 5
cmp /tmp/d9D5_n3036_haar_c69c22.edges records/d9D5_n3036_haar_c69c22.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n3036_haar_c69c22.edges     # 05305fe907f354997948eb0a8b98061dd5ecc1492c837716a531c03f99051ea9
python3 records/find_beta_meta.py 69 22 8 "$S"                                    # includes: 22 0 1
python3 records/build_metacyclic_cayley.py 69 22 8 22 0 1 "$S" /tmp/d9D5_n3036_haar_c69c22_cayley.edges 5
python3 src/canon_eq.py records/d9D5_n3036_haar_c69c22.edges /tmp/d9D5_n3036_haar_c69c22_cayley.edges
