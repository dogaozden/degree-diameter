#!/usr/bin/env python3
"""qeval.py QUOT SOL: weight and independence check of a quotient solution (quotient vertex ids, one per line)."""
import sys
from collections import Counter
W = []; adj = []
with open(sys.argv[1]) as f:
    n = int(f.readline())
    for i in range(n):
        a = list(map(int, f.readline().split()))
        W.append(a[0]); adj.append(set(a[2:2 + a[1]]))
S = [int(l) for l in open(sys.argv[2]) if l.strip() and not l.startswith('#')]
Sset = set(S)
ok = len(Sset) == len(S) and all(not (adj[v] & Sset) for v in S)
print('weight %d size %d independent %s weights %s' % (sum(W[v] for v in S), len(S), ok, sorted(Counter(W[v] for v in S).items())))
