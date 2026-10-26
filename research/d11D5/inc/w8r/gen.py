# W(8) version of squad r3 c4's generator: build n=586 bases from W(8) (w8_dm.in) by a point-line switch; sigma extended.
import random, sys
def load(fn):
    t = open(fn).read().split()
    n, dg = int(t[0]), int(t[1])
    ln = [[int(t[2 + l * dg + k]) for k in range(dg)] for l in range(n)]
    sig = [int(x) for x in t[2 + n * dg: 2 + n * dg + n]]
    return n, dg, ln, sig
def write(fn, n, dg, ln, sig):
    with open(fn, 'w') as f:
        f.write(f"{n} {dg}\n")
        for L in ln: f.write(" ".join(map(str, L)) + "\n")
        for s in sig: f.write(f"{s}\n")
n, dg, ln, sig = load('w8_dm.in')
pl = [[] for _ in range(n)]
for l in range(n):
    for p in ln[l]: pl[p].append(l)
col = [set() for _ in range(n)]          # collinear points
for L in ln:
    for p in L:
        col[p].update(L)
for p in range(n): col[p].discard(p)
lset = [set(L) for L in ln]
def disjoint_lines(a, b): return not (lset[a] & lset[b])
def gen_switch(kind, rng, K):
    """kind 'a': 8 lines L_i pairwise disjoint, p_i in L_i pairwise noncollinear; x* on L_i, l* through p_i.
       kind 'b': 7 lines, x* on l*, l* through p_i and x*."""
    while True:
        Ls = []
        cand = list(range(n)); rng.shuffle(cand)
        for l in cand:
            if all(disjoint_lines(l, m) for m in Ls): Ls.append(l)
            if len(Ls) == K: break
        if len(Ls) < K: continue
        ps = []
        order = [list(ln[l]) for l in Ls]
        for o in order: rng.shuffle(o)
        def rec(i, chosen):
            if i == K: return chosen
            for p in order[i]:
                if all(p not in col[q] and p != q for q in chosen):
                    r = rec(i + 1, chosen + [p])
                    if r: return r
            return None
        ps = rec(0, [])
        if ps: break
    return Ls, ps
def build(kind, rng, K=None):
    if K is None: K = dg if kind == 'a' else dg - 1
    Ls, ps = gen_switch(kind, rng, K)
    X = n; LS = n
    ln2 = [list(L) for L in ln] + [None]
    for L, p in zip(Ls, ps):
        ln2[L] = [X if q == p else q for q in ln2[L]]
    if kind == 'a':
        ln2[LS] = list(ps)
    else:
        ln2[LS] = list(ps) + [X]
        # x* must be on L_i as well (replace p_i by x*? no: x* is added, p_i removed) -> handled below
    return ln2, Ls, ps
