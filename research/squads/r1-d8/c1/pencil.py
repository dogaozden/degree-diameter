#!/usr/bin/env python3
"""Card c1 (pencil labels), squad round r1-d8.

Lift: base = H(q) (flags, voltage (0,0)) + hop 1 (point p -> line s1[p], voltage (1, l1(p)))
+ hop 2 (point p -> line s2[p], voltage (2, l2(p))) in Z_5 x Z_k, scored by liftdiam at D = 8.

Pencil value of a point p with coordinate vector v = H.P[p]:
  f, g: fixed random linear forms on GF(q)^7 (seeded).
  'cyc'   : F(v) = f(v) + theta g(v) in GF(q^2) (theta^2 = nonresidue); c(p) = dlog_gamma F(v) mod (q+1),
            i.e. PG(1,q) = GF(q^2)*/GF(q)* numbered cyclically (Z_{q+1}); special label q+1 if f=g=0.
  'slope' : c(p) = f(v)/g(v) in GF(q), infinity -> q, special (f=g=0) -> q+1.
Labels of hops are phi(c(p)) in Z_k, phi = mod k ('id'), or a seeded random table on the q+2 classes ('rnd'),
or independent random per point ('pt').

Usage: python3 pencil.py q k rule labspec seed [m2] [flagv]
  rule    : rand (random bijections) | inc (two disjoint 1-factors of H(q)'s incidence graph)
  labspec : cyc-id | cyc-rnd | slope-id | slope-rnd | pt
  m2      : multiplier of hop 2 labels relative to hop 1 (default 1)
  flagv   : zero | pencil (flag (p,L) gets Z_k voltage c(p) mod k, default zero)
"""
import os
import random
import subprocess
import sys

D8 = '/home/user/degree-diameter/research/theorems/d8'
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, D8)
import numpy as np  # noqa: E402
import gh  # noqa: E402
from models import perfect_matching  # noqa: E402

LIFT = os.path.join(HERE, 'liftdiam_fixed')  # copy of research/theorems/d8/liftdiam.c with the stall fix
TMP = os.path.join(HERE, 'tmp')


def gf_q2_dlog(q, nonres):
    """discrete log table of GF(q^2)* = GF(q)[theta]/(theta^2 - nonres): element (a,b) -> exponent of generator."""
    def mul(x, y):
        a, b = x
        c, d = y
        return ((a * c + nonres * b * d) % q, (a * d + b * c) % q)
    for a in range(q):
        for b in range(q):
            if (a, b) == (0, 0):
                continue
            z, seen = (1, 0), {}
            for e in range(q * q - 1):
                if z in seen:
                    break
                seen[z] = e
                z = mul(z, (a, b))
            if len(seen) == q * q - 1:
                return seen
    raise RuntimeError('no generator')


def pencil_classes(H, f, g, kind):
    """integer class in 0..q+1 per point (q+1 = special: f = g = 0)."""
    q = H.q
    P = np.asarray(H.P, dtype=np.int64)
    fv = ((P @ np.asarray(f, dtype=np.int64)) % q).tolist()
    gv = ((P @ np.asarray(g, dtype=np.int64)) % q).tolist()
    out = []
    if kind == 'cyc':
        dl = gf_q2_dlog(q, nonres=next(x for x in range(2, q) if pow(x, (q - 1) // 2, q) == q - 1))
        for a, b in zip(fv, gv):
            out.append(q + 1 if (a, b) == (0, 0) else dl[(a, b)] % (q + 1))
    elif kind == 'slope':
        for a, b in zip(fv, gv):
            if b:
                out.append(a * pow(b, -1, q) % q)
            elif a:
                out.append(q)
            else:
                out.append(q + 1)
    else:
        raise ValueError(kind)
    return out


def build(H, q, k, rule, labspec, seed, m2=1, flagv='zero'):
    rng = random.Random(seed)
    N = H.N
    # linear forms (fixed per seed)
    f = [rng.randrange(q) for _ in range(7)]
    g = [rng.randrange(q) for _ in range(7)]
    if labspec.startswith('cyc'):
        cls = pencil_classes(H, f, g, 'cyc')
    else:
        cls = pencil_classes(H, f, g, 'slope')
    ncls = q + 2
    if labspec.endswith('-id'):
        tab1 = [c % k for c in range(ncls)]
    elif labspec.endswith('-rnd'):
        tab1 = [rng.randrange(k) for _ in range(ncls)]
    if labspec == 'pt':
        l1 = [rng.randrange(k) for _ in range(N)]
        l2 = [rng.randrange(k) for _ in range(N)]
    else:
        l1 = [tab1[c] for c in cls]
        l2 = [(m2 * x) % k for x in l1]
    # hop matchings
    nbrs = [list(map(int, H.through[p])) for p in range(N)]
    if rule == 'rand':
        s1 = list(range(N))
        rng.shuffle(s1)
        s2 = list(range(N))
        rng.shuffle(s2)
    elif rule == 'inc':
        s1 = perfect_matching(N, nbrs, rng)
        s2 = perfect_matching(N, nbrs, rng, forbid=s1)
    else:
        raise ValueError(rule)
    edges = []
    for (p, L) in gh.flags(H):
        if flagv == 'pencil':
            edges.append((p, L, 0, cls[p] % k))
        else:
            edges.append((p, L, 0, 0))
    for p in range(N):
        edges.append((p, N + s1[p], 1, l1[p]))
        edges.append((p, N + s2[p], 2, l2[p]))
    return 2 * N, edges


def liftdiam(path, D=8, step=1):
    cmd = ['timeout', '900', 'nice', '-n', '10', LIFT, path, str(D), '1', str(step)]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    unr = int(out.split('unreached_pairs')[1].split()[0])
    ecc = out.split('max_ecc')[1].split()[0]
    return unr, ecc


def run(H, q, k, rule, labspec, seed, m2=1, flagv='zero', D=8, step=1):
    NB, edges = build(H, q, k, rule, labspec, seed, m2, flagv)
    os.makedirs(TMP, exist_ok=True)
    path = os.path.join(TMP, f'b_q{q}_k{k}_{rule}_{labspec}_m{m2}_{flagv}_s{seed}.txt')
    gh.write_base(path, NB, 5, k, edges)
    unr, ecc = liftdiam(path, D, step)
    os.remove(path)
    return unr, ecc


if __name__ == '__main__':
    q = int(sys.argv[1])
    k = int(sys.argv[2])
    rule, labspec, seed = sys.argv[3], sys.argv[4], int(sys.argv[5])
    m2 = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    flagv = sys.argv[7] if len(sys.argv) > 7 else 'zero'
    H = gh.load(q)
    unr, ecc = run(H, q, k, rule, labspec, seed, m2, flagv)
    print(f'q={q} M={5*k} k={k} rule={rule} labels={labspec} seed={seed} m2={m2} flagv={flagv} '
          f'unreached={unr} max_ecc={ecc}', flush=True)
