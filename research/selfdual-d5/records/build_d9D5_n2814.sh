#!/bin/bash
# Rebuild and check the (9,5) graph on 2,814 vertices (run from research/selfdual-d5/).
# Haar graph of G = C67 : C21 = <x, y | x^67 = y^21 = 1, y x y^-1 = x^29> (= SmallGroup(1407,2) = C7 x (C67 : C3); y acts
# with order 3), elements x^i y^j written (i,j); S = {(0,0), (51,0), (4,0), (22,10), (10,11), (44,5), (3,16), (55,19),
# (25,2)}; (g,A) ~ (s g, B).  S is self-dual: psi(g) = beta(g)^-1 with beta(x) = x^-1, beta(y) = y fixes (0,0), (51,0),
# (4,0) and swaps (22,10)-(10,11), (44,5)-(3,16), (55,19)-(25,2).
S="0,0 51,0 4,0 22,10 10,11 44,5 3,16 55,19 25,2"
# 1) GAP-free build from the formula + BFS from every vertex:
python3 records/build_metacyclic_haar.py 67 21 29 "$S" /tmp/d9D5_n2814.edges 5
# 2) all-pairs check with the coordinator's apsp.c (and the D-1 sanity check), and the independent Python checker:
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/d9D5_n2814.edges 9 5 | tail -1; /tmp/apsp /tmp/d9D5_n2814.edges 9 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d9D5_n2814.edges 9 5
cmp /tmp/d9D5_n2814.edges records/d9D5_n2814_haar_c67c21.edges && echo "identical to the saved edge list"
sha256sum records/d9D5_n2814_haar_c67c21.edges
# 3) the self-dual automorphism (search over x -> x^u, y -> x^t y^v) and the Cayley description over G : <tau>
#    (= C67 : C42), T = S tau; BFS from the identity; nauty-labelg gives the same canonical form as the saved edge list
python3 records/find_beta_meta.py 67 21 29 "$S"          # prints: 66 0 1
python3 records/build_metacyclic_cayley.py 67 21 29 66 0 1 "$S" /tmp/d9D5_n2814_cayley.edges 5
/tmp/apsp /tmp/d9D5_n2814_cayley.edges 9 5 | tail -1
python3 src/canon_eq.py records/d9D5_n2814_haar_c67c21.edges /tmp/d9D5_n2814_cayley.edges
# 4) the search that found it: gap -q -c 'N:=1407;; ID:=2;; OUT:="/tmp/g1407_2.ht";; NOEXT:=1;;' src/export_sd.g
#    K=9 SECS=2 DEEP=10,25 TYPES=1,3,5 src/sdtabu /tmp/g1407_2.ht all     (record 2, type (3,3); records/sg1407_2_tabu.out)
