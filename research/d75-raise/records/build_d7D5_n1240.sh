#!/bin/bash
# Rebuild and check the (7,5) graph on 1,240 vertices (run from research/d75-raise/).
# Haar graph of G = C31 : C20 = <x, y | x^31 = y^20 = 1, y x y^-1 = x^29> (= SmallGroup(620,1)), elements x^i y^j
# written (i,j); S = {(0,0), (1,10), (15,10), (27,17), (1,3), (13,2), (11,18)}; (g,A) ~ (s g, B).
# 1) GAP-free build from the formula + BFS from every vertex:
python3 records/build_metacyclic_haar.py 31 20 29 "0,0 1,10 15,10 27,17 1,3 13,2 11,18" /tmp/d7D5_n1240.edges 5
# 2) all-pairs check with the coordinator's apsp.c (and the D-1 sanity check), and the independent Python checker:
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c
/tmp/apsp /tmp/d7D5_n1240.edges 7 5 | tail -1; /tmp/apsp /tmp/d7D5_n1240.edges 7 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/d7D5_n1240.edges 7 5
cmp /tmp/d7D5_n1240.edges records/d7D5_n1240_haar_c31c20.edges && echo "identical to the saved edge list"
# 3) the search that found it (GAP + C): export SmallGroup(620,1) and run the self-dual orbit search
#    gap -q -c 'N:=620;; ID:=1;; OUT:="/tmp/g620_1.ht";;' src/export.g; gcc -O3 -o src/haar75 src/haar75.c -lm
#    MAXEV=8000000 src/haar75 /tmp/g620_1.ht anti     (9 solutions, type anti f 3 m 2)
