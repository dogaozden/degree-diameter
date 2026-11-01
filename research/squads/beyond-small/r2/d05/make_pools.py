#!/usr/bin/env python3
"""make_pools.py: poolA2/poolB2 = hubpack candidate pools (poolA/poolB) + hubs of earlier packings (deduplicated)."""
H = 16896
def load_pool(fn):
    L = open(fn).read().split('\n'); nc = int(L[0]); return [tuple(map(int, l.split()[1:])) for l in L[1:1 + nc]]
def load_hubs(fn, off):
    return [tuple(x - off for x in map(int, l.split())) for l in open(fn) if l.strip()]
def dedupe(lst):
    seen = set(); out = []
    for t in lst:
        k = tuple(sorted(t))
        if k not in seen: seen.add(k); out.append(t)
    return out
A2 = dedupe(load_pool('poolA.txt') + load_hubs('../hubsA_191.txt', H) + load_hubs('hubsA_pack.txt', H))
B2 = dedupe(load_pool('poolB.txt') + load_hubs('hubsB_6k.txt', 0) + load_hubs('hubsB_pack.txt', 0) + load_hubs('hubsB_a.txt', 0))
for name, lst in (('poolA2.txt', A2), ('poolB2.txt', B2)):
    with open(name, 'w') as f:
        f.write(f"{len(lst)}\n")
        for t in lst: f.write(f"{len(t)} " + " ".join(map(str, t)) + "\n")
    print(name, len(lst))
