#!/usr/bin/env python3
"""Keep a subset of automorphism generators with the same vertex orbits (greedy, in the given order).

usage: fewgens.py GENS.json OUT.json
The orbit BFS (gen_orbit2.py) needs only the orbits; fewer generators mean smaller permutation checks."""
import json, sys

gens = json.load(open(sys.argv[1]))
n = len(gens[0])


def orbits(gs):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in gs:
        for v in range(n):
            a, b = f(v), f(g[v])
            if a != b:
                par[a] = b
    return len({f(v) for v in range(n)}), f


target, _ = orbits(gens)
keep = []
cur = n
for g in gens:
    c, _ = orbits(keep + [g])
    if c < cur:
        keep.append(g)
        cur = c
    if cur == target:
        break
assert cur == target
json.dump(keep, open(sys.argv[2], 'w'))
print(f'{len(gens)} generators -> {len(keep)}, {target} orbits', file=sys.stderr)
