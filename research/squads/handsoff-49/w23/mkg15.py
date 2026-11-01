#!/usr/bin/env python3
"""w15 group builder: semidirect products P x|_phi Z_4 (order 4|P|), as tables for haar_tab (tab FILE.bin).

(v,a)(w,b) = (v * phi^a(w), a+b), phi an automorphism of P of order dividing 4. Table layout as groups.py:
int32 N, then N*N uint16 (row g: g*h), identity index 0.
Library use: from mkg15 import abelian_P, semidirect, heis_P, invariants, write_bin
"""
import sys, itertools
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/tools")
import groups as GR

write_bin = GR.write_bin


def abelian_P(moduli):
    """P = Z_n1 x ... x Z_nr. Returns (TP, coords) with TP the addition table (identity 0)."""
    moduli = list(moduli)
    r = len(moduli)
    Pn = int(np.prod(moduli))
    C = np.zeros((Pn, r), dtype=np.int64)
    rem = np.arange(Pn)
    for i in range(r - 1, -1, -1):          # mixed radix, coordinate 0 most significant
        C[:, i] = rem % moduli[i]
        rem //= moduli[i]
    mods = np.array(moduli)
    weights = np.ones(r, dtype=np.int64)
    for i in range(r - 2, -1, -1):
        weights[i] = weights[i + 1] * moduli[i + 1]
    S = (C[:, None, :] + C[None, :, :]) % mods
    TP = (S @ weights).astype(np.int64)
    return TP.astype(np.int64), C


def abelian_auto(moduli, A):
    """Permutation x -> A x (A integer r x r matrix) on P = prod Z_{n_i}; checks it is an automorphism."""
    TP, C = abelian_P(moduli)
    mods = np.array(moduli)
    weights = np.ones(len(moduli), dtype=np.int64)
    for i in range(len(moduli) - 2, -1, -1):
        weights[i] = weights[i + 1] * moduli[i + 1]
    A = np.array(A, dtype=np.int64)
    img = (C @ A.T) % mods
    perm = (img @ weights).astype(np.int64)
    assert len(set(perm.tolist())) == len(perm), "not a bijection"
    assert perm[0] == 0
    # homomorphism check on the whole table
    assert (perm[TP] == TP[perm][:, perm]).all(), "not a homomorphism"
    return TP, perm


def heis_P(p, extra):
    """Heis(p) x Z_extra as table; coords per index: (x, y, z, w)."""
    TP = GR.table(f"heis {p} x cyc {extra}")
    return TP


def coords_heis(p, extra):
    els = [(0, 0, 0)] + [t for t in itertools.product(range(p), repeat=3) if t != (0, 0, 0)]
    out = []
    for a in range(len(els)):
        for b in range(extra):
            out.append(els[a] + (b,))
    return out


def index_of(coords_list):
    return {c: i for i, c in enumerate(coords_list)}


def semidirect(TP, phi, order_t=4):
    """TP: table of P (identity 0); phi: permutation array of P (automorphism, phi^4 = id). Returns table of P x| Z_4."""
    Pn = len(TP)
    powers = [np.arange(Pn)]
    for _ in range(1, order_t):
        powers.append(phi[powers[-1]])
    assert (phi[powers[-1]] == np.arange(Pn)).all(), "phi^4 != id"
    N = Pn * order_t
    T = np.empty((N, N), dtype=np.uint16)
    for a in range(order_t):
        for b in range(order_t):
            blk = TP[:, powers[a]] + Pn * ((a + b) % order_t)
            T[a * Pn:(a + 1) * Pn, b * Pn:(b + 1) * Pn] = blk.astype(np.uint16)
    return T


def check_automorphism(TP, phi):
    assert (phi[TP] == TP[phi][:, phi]).all(), "phi is not an automorphism"


def invariants(T):
    """order, centre size, |G/G'|, number of involutions, element-order histogram (small dict)."""
    N = len(T)
    inv = np.empty(N, dtype=np.int64)
    rows, cols = np.nonzero(T == 0)
    inv[rows] = cols
    centre = int(((T == T.T).all(axis=1)).sum())
    X = np.arange(N)
    cs = np.unique(T[T[inv[:, None], inv[None, :]], T[X[:, None], X[None, :]]].ravel())
    gens = cs.tolist()
    Hset = {0}
    frontier = [0]
    while frontier:
        new = []
        for h in frontier:
            for g in gens:
                k = int(T[h, g])
                if k not in Hset:
                    Hset.add(k)
                    new.append(k)
        frontier = new
    ab = N // len(Hset)
    o = np.zeros(N, dtype=np.int64)
    o[0] = 1
    pw = np.arange(N)
    done = np.zeros(N, dtype=bool)
    done[0] = True
    for k in range(1, 2 * N):
        pw = T[pw, X]             # g^(k+1)
        newly = (pw == 0) & (~done)
        o[newly] = k + 1          # pw holds g^(k+1) after k steps
        done |= newly
        if done.all():
            break
    hist = {}
    for v in o.tolist():
        hist[v] = hist.get(v, 0) + 1
    return dict(N=N, centre=centre, ab=ab, invol=hist.get(2, 0), hist=hist, maxord=int(o.max()))


def fmt_hist(h):
    return ",".join(f"{k}:{v}" for k, v in sorted(h.items()))
