#!/bin/bash
# Rebuild and check the (7,5) graph on 1,200 vertices (run from research/beyond-haar-d5/).
# 1) as a Haar graph of SL(2,5) x Z5 (repo checker, builds the group from its definition):
python3 ../frontier/build_haar2.py records/d7D5_n1200_haar_sl5xc5.txt /tmp/d7D5_n1200_haar.edges
# 2) as a coset graph of SmallGroup(1200,475) from the saved permutation data (GAP-free):
python3 coset/dc2_edges.py records/sg1200_475_h2.dc2 /tmp/d7D5_n1200_coset.edges 242 206 265 2
# all-pairs checks (no symmetry assumed), and the D-1 sanity check
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c
for f in /tmp/d7D5_n1200_haar.edges /tmp/d7D5_n1200_coset.edges; do /tmp/apsp $f 7 5 | tail -1; /tmp/apsp $f 7 4 | tail -1; done
python3 records/check_independent.py /tmp/d7D5_n1200_coset.edges 7 5
