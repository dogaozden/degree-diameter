"""Bipartite coset graphs Cos(G; A, B): vertices G/A and G/B (left cosets), gA ~ hB iff gA ∩ hB nonempty.
G acts edge-transitively; with A ∩ B = 1 and |A| = |B| = Δ the graph is Δ-regular on 2|G|/Δ vertices, and
diameter <= D  <=>  (AB)^(D/2) = G (D even), or (AB)^k A = G and (BA)^k B = G (D = 2k+1).
Conder's (3,7) record (168 vertices, |Aut| = 504) is of this form with |G| = 252, A, B = Z3.
Here A = <a>, B = <b> cyclic of order Δ; G a permutation group given by generators (we use matrix groups acting on
the projective line / vectors, converted to permutations), enumerated by closure.
usage: python3 coset.py GROUP Δ D [samples] [seed]     GROUP: psl:q pgl:q sl:q (q prime), x:n suffix = times Z_n
"""
import sys, random
import numpy as np
from collections import deque


def mat_group(kind, q):
    """elements as tuples (a,b,c,d) mod q, canonical up to the centre for psl/pgl"""
    def canon(m):
        a, b, c, d = m
        if kind == 'sl':
            return m
        if kind == 'psl':
            n = tuple((-x) % q for x in m)
            return min(m, n)
        f = a if a else b
        iv = pow(f, q - 2, q)
        return tuple(x * iv % q for x in m)
    els = []
    for a in range(q):
        for b in range(q):
            for c in range(q):
                for d in range(q):
                    det = (a * d - b * c) % q
                    if (kind in ('sl', 'psl') and det == 1) or (kind == 'pgl' and det != 0):
                        els.append(canon((a, b, c, d)))
    els = sorted(set(els))
    def mul(x, y):
        a, b, c, d = x; e, f, g, h = y
        return canon(((a * e + b * g) % q, (a * f + b * h) % q, (c * e + d * g) % q, (c * f + d * h) % q))
    return els, mul, canon((1, 0, 0, 1))


def build(spec):
    parts = spec.split('x:')
    kind, q = parts[0].split(':'); q = int(q)
    n = int(parts[1]) if len(parts) > 1 else 1
    els, mul, e = mat_group(kind, q)
    if n > 1:
        E = [(x, z) for x in els for z in range(n)]
        def mul2(u, v): return (mul(u[0], v[0]), (u[1] + v[1]) % n)
        return E, mul2, (e, 0)
    return els, mul, e


def order(x, mul, e, cap=10000):
    y, k = x, 1
    while y != e:
        y = mul(y, x); k += 1
        if k > cap: return None
    return k


def coset_graph_diam(G, idx, Ra, Rb, Dl, e_i):
    """Ra, Rb: index arrays of right multiplication by a, b.  Returns (diameter, #vertices) of Cos(G;<a>,<b>) or None if
    disconnected / intersection nontrivial."""
    n = len(G)
    def labels(R):
        lab = np.full(n, -1, dtype=np.int64)
        nl = 0
        for i in range(n):
            if lab[i] < 0:
                j = i
                while lab[j] < 0:
                    lab[j] = nl; j = R[j]
                nl += 1
        return lab, nl
    la, na = labels(Ra)
    lb, nb = labels(Rb)
    if na != nb or na * (n // na) != n:
        return None
    # edges: g -> (la[g], lb[g]); A ∩ B = 1 iff every edge is hit by exactly one g
    edges = la * nb + lb
    if len(np.unique(edges)) != n:
        return None            # A ∩ B != 1 (multi-edges)
    adjA = [[] for _ in range(na)]
    adjB = [[] for _ in range(nb)]
    for g in range(n):
        adjA[la[g]].append(lb[g]); adjB[lb[g]].append(la[g])
    ecc = 0
    for side, s in ((0, la[e_i]), (1, lb[e_i])):
        dA = [-1] * na; dB = [-1] * nb
        (dA if side == 0 else dB)[s] = 0
        front = [s]; cur = side; lev = 0
        while front:
            lev += 1
            nxt = []
            if cur == 0:
                for u in front:
                    for w in adjA[u]:
                        if dB[w] < 0: dB[w] = lev; nxt.append(w)
            else:
                for u in front:
                    for w in adjB[u]:
                        if dA[w] < 0: dA[w] = lev; nxt.append(w)
            front = nxt; cur ^= 1
        if min(dA) < 0 or min(dB) < 0:
            return None
        ecc = max(ecc, max(dA), max(dB))
    return ecc, na + nb


def main():
    spec, Dl, Dmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    samples = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
    G, mul, e = build(spec)
    idx = {g: i for i, g in enumerate(G)}
    n = len(G)
    ordD = [g for g in G if order(g, mul, e, Dl + 1) == Dl]
    print(f"{spec}: |G| = {n}, elements of order {Dl}: {len(ordD)}, vertices of Cos = {2 * n // Dl}")
    if not ordD:
        return
    def R(x): return np.array([idx[mul(g, x)] for g in G], dtype=np.int64)
    # a: one representative per conjugacy class (cheap: just take a few distinct ones), b: all or sampled
    a_list = []
    seen = set()
    for g in ordD:
        if g in seen: continue
        cls = {mul(mul(h, g), G[idx[h]] if False else inv(h, mul, e, G, idx)) for h in G[:0]}
        a_list.append(g)
        if len(a_list) >= 3: break
    best = {}
    tried = 0
    for a in a_list[:1]:
        Ra = R(a)
        bl = ordD if not samples else rng.sample(ordD, min(samples, len(ordD)))
        for b in bl:
            tried += 1
            res = coset_graph_diam(G, idx, Ra, R(b), Dl, idx[e])
            if res is None: continue
            dm, nv = res
            best[dm] = best.get(dm, 0) + 1
    print(f"  pairs tried {tried}; diameters found (diameter: count) {dict(sorted(best.items()))}")


def inv(h, mul, e, G, idx):
    return None


if __name__ == '__main__':
    main()
