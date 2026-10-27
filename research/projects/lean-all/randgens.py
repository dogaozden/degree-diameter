#!/usr/bin/env python3
"""Replace many automorphism generators by K random products with the same vertex orbits (seeded, deterministic).

usage: randgens.py GENS.json OUT.json [--seed S] [--k K]
Each element is the product, over 3 rounds, of a random half of the generators in random order. Orbits are checked
here; gen_orbit2.py and the Lean check re-verify that every element is an automorphism."""
import argparse, json, random

ap = argparse.ArgumentParser()
ap.add_argument('gens'); ap.add_argument('out')
ap.add_argument('--seed', type=int, default=7); ap.add_argument('--k', type=int, default=2)
args = ap.parse_args()
gens = json.load(open(args.gens))
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
    return len({f(v) for v in range(n)})


random.seed(args.seed)
els = []
for _ in range(args.k):
    e = list(range(n))
    for _ in range(3):
        order = [g for g in gens if random.random() < 0.5]
        random.shuffle(order)
        for g in order:
            e = [g[e[x]] for x in range(n)]
    els.append(e)
t, c = orbits(gens), orbits(els)
assert c == t, (c, t)
json.dump(els, open(args.out, 'w'))
print(f'{len(gens)} generators -> {len(els)} random products, {t} orbits')
