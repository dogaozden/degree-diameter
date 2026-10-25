#!/usr/bin/env python3
# Card c2: Z_5 x Z_k level skeleton on the incidence graph I of W(q) plus two point-line matchings.
# Lift group Z_m with m = 5k, k coprime to 5, so Z_m = Z_5 x Z_k (CRT). A voltage v has level v mod 5 and sheet v mod k.
#   flags:      level 0
#   matching 1: level 1 (cls 100)      matching 2: level 2 (cls 101)
#   sheet parts: random. Variant A: flags are exactly 0 and fixed (cls 0), sheets only on matchings.
#                Variant B: flags carry sheet parts 5*r (cls 1, annealable with FIXMOD=5).
# Level-preserving moves: baselift FIXMOD=5 keeps v mod 5, and matching swaps keep each edge's voltage.
#
# usage: python3 -B build.py q k seed variant OUT.base
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/d16D8')
import gq


def build(q, k, seed, variant):
    assert k % 5 != 0 and k >= 1
    m = 5 * k
    G = gq.load(q)
    N = G['N']
    rnd = random.Random(seed)
    edges = []
    for l, L in enumerate(G['lines']):
        for p in L:
            if variant == 'A':
                edges.append((p, N + l, 0, 0))
            else:
                edges.append((p, N + l, 5 * rnd.randrange(k), 1))
    for lev, cls in ((1, 100), (2, 101)):
        perm = list(range(N))
        rnd.shuffle(perm)
        for p in range(N):
            r = rnd.randrange(k)
            edges.append((p, N + perm[p], (lev + 5 * r) % m, cls))
    return 2 * N, m, edges


if __name__ == '__main__':
    q, k, seed, variant, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    V, m, E = build(q, k, seed, variant)
    with open(out, 'w') as f:
        f.write('%d %d %d\n' % (V, m, len(E)))
        f.write(''.join('%d %d %d %d\n' % e for e in E))
    print('wrote', out, 'V=%d m=%d E=%d' % (V, m, len(E)))
