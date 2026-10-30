#!/bin/bash
# Rebuild and check the (7,5) graph on 1,312 vertices (run from research/d75-raise/).
# Haar graph of G = C41 : C16 = <x, y | x^41 = y^16 = 1, y x y^-1 = x^38> (= SmallGroup(656,28)), elements x^i y^j
# written (i,j); S = {(0,0), (3,8), (18,8), (14,3), (1,5), (32,14), (1,2)}; (g,A) ~ (s g, B).
# 1) GAP-free build from the formula + BFS from every vertex:
python3 records/build_metacyclic_haar.py 41 16 38 "0,0 3,8 18,8 14,3 1,5 32,14 1,2" /tmp/d7D5_n1312.edges 5
# 2) all-pairs check with the coordinator's apsp.c (and the D-1 sanity check), and the independent Python checker:
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c
/tmp/apsp /tmp/d7D5_n1312.edges 7 5 | tail -1; /tmp/apsp /tmp/d7D5_n1312.edges 7 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d7D5_n1312.edges 7 5
cmp /tmp/d7D5_n1312.edges records/d7D5_n1312_haar_c41c16.edges && echo "identical to the saved edge list"
# 3) the search that found it (GAP + C): export SmallGroup(656,28) and run the self-dual orbit search
#    gap -q -c 'N:=656;; ID:=28;; OUT:="/tmp/g656_28.ht";;' src/export.g; gcc -O3 -o src/haar75 src/haar75.c -lm
#    MAXEV=100000000 MAXEVF=8000000 src/haar75 /tmp/g656_28.ht anti     (9 solutions, type anti f 3 m 2)
# 4) second description: Cayley graph of a group of order 1,312 (G : <t>, t x t = x^-1, t y t = y^9), BFS from the
#    identity; nauty-labelg gives the same canonical form as the saved edge list
python3 records/build_d7D5_n1312_cayley.py /tmp/d7D5_n1312_cayley.edges
/tmp/apsp /tmp/d7D5_n1312_cayley.edges 7 5 | tail -1
