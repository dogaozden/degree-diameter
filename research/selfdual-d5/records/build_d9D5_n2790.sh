#!/bin/bash
# Rebuild and check the (9,5) graph on 2,790 vertices (run from research/selfdual-d5/).
# Haar graph of G = C31 : C45 = <x, y | x^31 = y^45 = 1, y x y^-1 = x^28> (= SmallGroup(1395,1); y acts with order 15),
# elements x^i y^j written (i,j); S = {(0,0), (28,20), (18,25), (24,26), (22,19), (21,28), (3,17), (10,41), (4,4)};
# (g,A) ~ (s g, B).  S is self-dual: psi(g) = beta(g)^-1 with beta(x) = x^-1, beta(y) = y fixes (0,0) and swaps the
# four pairs (28,20)-(18,25), (24,26)-(22,19), (21,28)-(3,17), (10,41)-(4,4).
# 1) GAP-free build from the formula + BFS from every vertex:
python3 records/build_metacyclic_haar.py 31 45 28 "0,0 28,20 18,25 24,26 22,19 21,28 3,17 10,41 4,4" /tmp/d9D5_n2790.edges 5
# 2) all-pairs check with the coordinator's apsp.c (and the D-1 sanity check), and the independent Python checker:
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c
/tmp/apsp /tmp/d9D5_n2790.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n2790.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n2790.edges 9 5
cmp /tmp/d9D5_n2790.edges records/d9D5_n2790_haar_c31c45.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n2790_haar_c31c45.edges   # 5d63f5bee169b51c1fbe38ab0ca7971c35460b7f73e8cf25884db9cc21b9b6b7
# 3) second description: Cayley graph of C31 : C90 = G : <t> (t x t = x^-1, t y t = y), T = S t, BFS from the
#    identity; nauty-labelg gives the same canonical form as the saved edge list (src/canon_eq.py)
python3 records/build_d9D5_n2790_cayley.py /tmp/d9D5_n2790_cayley.edges
/tmp/apsp /tmp/d9D5_n2790_cayley.edges 9 5 | tail -1
python3 src/canon_eq.py records/d9D5_n2790_haar_c31c45.edges /tmp/d9D5_n2790_cayley.edges
# 4) the search that found it (GAP + C): export SmallGroup(1395,1) (no non-split records needed for odd valency) and
#    run the self-dual tabu over every involution class and type (1,4), (3,3), (5,2):
#    gap -q -c 'N:=1395;; ID:=1;; OUT:="/tmp/g1395_1.ht";; NOEXT:=1;;' src/export_sd.g; gcc -O3 -o src/sdtabu src/sdtabu.c
#    K=9 SECS=2 DEEP=10,25 TYPES=1,3,5 src/sdtabu /tmp/g1395_1.ht all      (record 1, type (1,4); found within 27 s)
