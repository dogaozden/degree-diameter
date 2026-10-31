#!/usr/bin/env python3
"""meta_prio.py LIST: sort a meta_list.py list (n m k r d) for a sweep: prime m first, then small center
(k/d, the order of <y^d>), then n.  Keeps m >= MINM (env, default 31)."""
import os, sys
minm = int(os.environ.get("MINM", 31))
def isprime(p):
    return p > 1 and all(p % q for q in range(2, int(p ** 0.5) + 1))
rows = [l.split() for l in open(sys.argv[1]) if l.strip()]
rows = [r for r in rows if int(r[1]) >= minm]
rows.sort(key=lambda r: (not isprime(int(r[1])), int(r[2]) // int(r[4]) > 8, int(r[0]), -int(r[4])))
for r in rows: print(" ".join(r))
