#!/usr/bin/env python3
"""fam5.py: families of 5-spaces W = ker f1 cap ker f2 (linear forms over GF(q)) and their singular points.

Card e14 (D = 9 point classes). Every 5-space W of F_q^7 has W cap Q(6,q) meeting every plane pi_p (3-dim totally
singular), so each W cap Q is a dominating point class. Writes:
  - an int32 colour file (class index per point, -1 = not covered) from a greedy minimal-overlap family of K
    5-spaces with overlap points given to one class (argument 'assign').
Usage: python3 fam5.py Q K SEED OUT [CANDIDATES]
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

HEXDIR = '/home/user/degree-diameter/research/theorems/polylev/hex'


def load(q):
    return Hex(f'{HEXDIR}/hex_q{q}.bin')


def lin(H, f):
    """value of the linear form f (length 7) at every point, in GF(q)."""
    acc = np.zeros(H.N, dtype=np.int64)
    for j in range(7):
        if f[j]:
            acc = H.ADD[acc, H.MUL[f[j], H.coord[:, j]]]
    return acc


def section(H, forms):
    m = np.ones(H.N, dtype=bool)
    for f in forms:
        m &= lin(H, f) == 0
    return m


def planes(H):
    """PI[p] = the q^2+q+1 points equal or collinear to p (the plane pi_p)."""
    out = np.zeros((H.N, H.q * H.q + H.q + 1), dtype=np.int64)
    for p in range(H.N):
        out[p] = np.unique(H.lines[H.PL[p]].ravel())
    return out


def dominating(PI, mask):
    return bool(mask[PI].any(axis=1).all())


def family(H, K, rng, cand=300):
    """greedy: each new 5-space minimises the number of points it shares with the chosen ones (sum of C(c,2))."""
    q = H.q
    cover = np.zeros(H.N, dtype=np.int64)
    masks = []
    for _ in range(K):
        best, bm = None, None
        for _ in range(cand):
            f1 = rng.integers(0, q, 7); f2 = rng.integers(0, q, 7)
            if not f1.any() or not f2.any():
                continue
            m = section(H, [f1, f2])
            if m.sum() == 0:
                continue
            score = int(cover[m].sum())  # points already covered once or more by chosen 5-spaces
            score2 = int((m & (cover >= 1)).sum())
            key = (score, score2, rng.random())
            if best is None or key < best:
                best, bm = key, m
        masks.append(bm)
        cover += bm
    return masks, cover


def assign(masks, rng):
    """each covered point goes to one of the classes containing it; the class with fewer points so far wins."""
    K = len(masks)
    N = masks[0].shape[0]
    col = -np.ones(N, dtype=np.int32)
    size = np.zeros(K, dtype=np.int64)
    M = np.array(masks)  # K x N
    for x in rng.permutation(N):
        cs = np.where(M[:, x])[0]
        if len(cs) == 0:
            continue
        c = cs[np.argmin(size[cs] + rng.random(len(cs)))]
        col[x] = c
        size[c] += 1
    return col


if __name__ == '__main__':
    q, K, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    cand = int(sys.argv[5]) if len(sys.argv) > 5 else 300
    rng = np.random.default_rng(seed)
    H = load(q)
    PI = planes(H)
    masks, cover = family(H, K, rng, cand)
    sizes = [int(m.sum()) for m in masks]
    print('class section sizes', sizes[:5], '...', 'min', min(sizes), 'max', max(sizes))
    print('covered points', int((cover >= 1).sum()), 'of', H.N, '; multiplicity histogram', np.bincount(cover)[:6].tolist())
    print('all sections dominating:', all(dominating(PI, m) for m in masks))
    col = assign(masks, rng)
    col.astype(np.int32).tofile(out)
    # domination count per class after assignment
    ok = 0
    for c in range(K):
        if dominating(PI, col == c):
            ok += 1
    print('after assignment: classes dominating', ok, 'of', K)
