"""Write a Haar controller H(G,S) as a general controller edge list for ctrl_anneal: lines "a b" meaning A-vertex a
(group element a) -- B-vertex b (element s a).  usage: python3 haar_ctrl_edges.py "<group spec>" "s0 s1 s2 s3" out"""
import sys
import controller as ct
T = ct.parse(sys.argv[1]); S = list(map(int, sys.argv[2].split()))
with open(sys.argv[3], 'w') as f:
    for g in range(len(T)):
        for s in S:
            f.write(f"{g} {int(T[s, g])}\n")
