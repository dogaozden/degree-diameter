#!/usr/bin/env python3
"""check_q.py QUOT SOL: quotient-level check of a solution (quotient ids, one per line): distinct, in range, pairwise
non-adjacent in the quotient (both directions), prints the total orbit weight."""
import sys
q, s = sys.argv[1], sys.argv[2]
with open(q) as f:
    n = int(f.readline())
    w = [0] * n
    nb = [None] * n
    for i in range(n):
        a = list(map(int, f.readline().split()))
        w[i] = a[0]
        nb[i] = set(a[2:2 + a[1]])
sol = [int(x) for x in open(s) if x.strip() and not x.startswith('#')]
S = set(sol)
bad = sum(1 for a in sol for b in nb[a] if b in S)
ok = len(S) == len(sol) and all(0 <= v < n for v in sol) and bad == 0
print('%s quotient=%d weight=%d distinct=%s independent=%s' % ('VALID' if ok else 'INVALID', len(sol), sum(w[v] for v in sol),
      len(S) == len(sol), bad == 0))
