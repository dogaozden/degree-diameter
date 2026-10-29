"""A hub graph for the (15,7) build: the Haar graph of PSL(2,p) with a set S of 8 elements.
Line-side hub x ~ point-side hub x s (x in G, s in S). Same-side distances <= 6 hold iff (S S^-1)^3 = G (line side) and
(S^-1 S)^3 = G (point side), checked here by BFS on G.  Output: K = |G| and the edge list "a b" (a line-side index,
b point-side index), for tm_build_herm.py.
Usage: python psl_hubgraph.py p SEED OUT"""
import sys
import itertools
import numpy as np

p, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]


def canon(m):
    a, b, c, d = m
    # PSL: identify m and -m; choose the representative with the first nonzero entry <= (p-1)/2
    for x in (a, b, c, d):
        if x % p:
            if x % p > (p - 1) // 2:
                return tuple((-y) % p for y in m)
            return tuple(y % p for y in m)


els = []
for a, b, c in itertools.product(range(p), repeat=3):
    # d from ad - bc = 1 when a != 0, else enumerate
    if a:
        d = (1 + b * c) * pow(a, p - 2, p) % p
        els.append(canon((a, b, c, d)))
    else:
        if b == 0:
            continue
        for d in range(p):
            if (a * d - b * c) % p == 1:
                els.append(canon((a, b, c, d)))
els = sorted(set(els))
idx = {m: i for i, m in enumerate(els)}
G = len(els)
assert G == p * (p * p - 1) // 2, G


def mul(m, n):
    a, b, c, d = m; e, f, g, h = n
    return canon((a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h))


def inv(m):
    a, b, c, d = m
    return canon((d, -b, -c, a))


rng = np.random.default_rng(seed)
ID = canon((1, 0, 0, 1))


def coverage(S):
    worst = G
    for side in (0, 1):
        D = {mul(s, inv(t)) if side == 0 else mul(inv(s), t) for s in S for t in S}
        reach = {ID}
        for _ in range(3):
            reach = {mul(x, d) for x in reach for d in D}
        worst = min(worst, len(reach))
    return worst


S = [els[i] for i in rng.choice(G, size=8, replace=False)]
cov = coverage(S)
it = 0
while cov < G and it < 3000:                 # hill climbing: replace one generator, keep if coverage does not drop
    it += 1
    T = list(S); T[rng.integers(8)] = els[rng.integers(G)]
    if len(set(T)) < 8:
        continue
    c = coverage(T)
    if c >= cov:
        if c > cov:
            print(f'  step {it}: coverage {c} of {G}', flush=True)
        S, cov = T, c
assert cov == G, f'coverage {cov} of {G}'
ok, attempt = True, it
with open(out, 'w') as f:
    f.write(f'{G}\n')
    for x in els:
        for s in S:
            f.write(f'{idx[x]} {idx[mul(x, s)]}\n')
print(f'PSL(2,{p}): |G| = {G}, S found at attempt {attempt}; same-side distances <= 6 on both sides; wrote {out}')
