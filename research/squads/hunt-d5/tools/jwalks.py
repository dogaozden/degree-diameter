#!/usr/bin/env python3
"""How evenly does a Haar connection set S spread its 4-step products over the cosets of G' (hunt-d5)?

For G = (Z_p x|_r Z_k) x Z_n with r != 1, G' = Z_p and G/G' = Z_k x Z_n, so the coset of s_a^-1 s_b s_c^-1 s_d depends
only on the (j, z) parts of the four elements. W_t = number of words e, s_a^-1 s_b (a != b) and s_a^-1 s_b s_c^-1 s_d
(a != b, b != c, c != d) landing in coset t; in the random model the coset t misses about p exp(-W_t / p) elements, and
mu_J = sum_t p exp(-W_t / p) is the expected cost of one side once the (j, z) parts are fixed (the other side is the
mirror image t -> -t, same mu_J).

Usage: jwalks.py SOLFILE...     (haar_fast solution files: header "d 5 meta p k r n c N ...", lines "idx meta(a=..,j=..) z=..")
       jwalks.py --random d p k r n SAMPLES SEED
"""
import itertools, math, random, re, sys

def mu_of(J, p, k, n):
    d = len(J); W = {}
    def add(t): W[t] = W.get(t, 0) + 1
    add((0, 0))
    for a, b in itertools.permutations(range(d), 2):
        add(((J[b][0] - J[a][0]) % k, (J[b][1] - J[a][1]) % n))
    for a in range(d):
        for b in range(d):
            if b == a: continue
            for c in range(d):
                if c == b: continue
                for e in range(d):
                    if e == c: continue
                    add(((-J[a][0] + J[b][0] - J[c][0] + J[e][0]) % k, (-J[a][1] + J[b][1] - J[c][1] + J[e][1]) % n))
    cells = [(x, y) for x in range(k) for y in range(n)]
    ws = [W.get(t, 0) for t in cells]
    return sum(p * math.exp(-w / p) for w in ws), min(ws), max(ws)

def read_sol(fn):
    lines = open(fn).read().split('\n')
    h = lines[0].split(); d = int(h[0]); i = h.index('meta'); p, k, r = map(int, h[i + 1:i + 4]); n = int(h[h.index('n') + 1])
    J = []
    for l in lines[1:]:
        m = re.search(r'j=(\d+)\) z=(\d+)', l)
        if m: J.append((int(m.group(1)), int(m.group(2))))
    assert len(J) == d, fn
    return d, p, k, n, J

if __name__ == '__main__':
    if sys.argv[1] == '--random':
        d, p, k, r, n, ns, seed = map(int, sys.argv[2:9]); rng = random.Random(seed)
        vals = sorted(mu_of([(rng.randrange(k), rng.randrange(n)) for _ in range(d)], p, k, n)[0] for _ in range(ns))
        print(f'random d={d} p={p} k={k} n={n}: mu_J min {vals[0]:.1f}  10% {vals[ns // 10]:.1f}  median {vals[ns // 2]:.1f}'
              f'  (uniform W: {p * k * n * math.exp(-(1 + d * (d - 1) + d * (d - 1) ** 3) / (p * k * n)):.1f})')
    else:
        for fn in sys.argv[1:]:
            d, p, k, n, J = read_sol(fn); mu, lo, hi = mu_of(J, p, k, n)
            print(f'{fn}: mu_J {mu:.1f}  W_t min {lo} max {hi}  (p = {p})  J = {sorted(J)}')
