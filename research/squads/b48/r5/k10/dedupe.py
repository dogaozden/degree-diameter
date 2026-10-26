import sys, itertools
from math import gcd
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
from gen import conj_classes
cands = []
for N in range(85, 101):
    for m in range(2, N + 1):
        if N % m: continue
        k = N // m
        if k < 2: continue
        for r in range(1, m):
            if gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append(f"meta {m} {k} {r}")
extra = ["dih 48", "dih 45", "sl2 3 x cyc 4", "agl1 5 x cyc 5", "A4x cyc8", "perm 4 1,0,2,3 ; 1,2,3,0 x cyc 4"]
def inv(spec):
    T = groups.table(spec).astype(np.int64)
    N = T.shape[0]
    e = 0
    ords = []
    for g in range(N):
        x, o = g, 1
        while x != e: x = T[x, g]; o += 1
        ords.append(o)
    cen = sum(1 for g in range(N) if all(T[g, h] == T[h, g] for h in range(N)))
    nc = len(conj_classes(groups.table(spec)))
    # number of squares / involutions etc.
    from collections import Counter
    oc = tuple(sorted(Counter(ords).items()))
    return (N, oc, cen, nc)
seen = {}
for s in cands + extra:
    try:
        key = inv(s)
    except Exception as ex:
        print("skip", s, ex, file=sys.stderr); continue
    seen.setdefault(key, []).append(s)
print(len(cands), "meta candidates;", len(seen), "invariant classes", file=sys.stderr)
with open("groups_k10.txt", "w") as f:
    for key, lst in sorted(seen.items(), key=lambda kv: (kv[0][0], kv[1][0])):
        f.write(f"{key[0]}\t{lst[0]}\t{len(lst)}\n")
