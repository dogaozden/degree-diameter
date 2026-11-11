#!/usr/bin/env python3
"""mkbase.py k "s0,s1,s2,s3" BASE PERM : Haar(Z_k,S) as a lift base (sides 0..k-1 and k..2k-1), rotation perm of order k."""
import sys
k = int(sys.argv[1]); S = [int(x) for x in sys.argv[2].split(',')]
assert len(set(s % k for s in S)) == 4
edges = [(i, k + (i + s) % k) for s in S for i in range(k)]
with open(sys.argv[3], 'w') as f:
    f.write(f"{2*k}\n" + "".join(f"{u} {v}\n" for u, v in edges))
perm = [(i + 1) % k for i in range(k)] + [k + (i + 1) % k for i in range(k)]
with open(sys.argv[4], 'w') as f:
    f.write(" ".join(map(str, perm)) + "\n")
