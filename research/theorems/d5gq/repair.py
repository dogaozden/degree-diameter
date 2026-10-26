"""One-transition repair tests (Definition 3.2 / Theorem E of D5_QUADRANGLE.md).

A transition goes from a level of type tj to a level of type tj2.  Element ids 0..np-1 are points, np..np+nl-1 lines.
M is an array over the A-elements of the source (local index: point id if A = points, line id if A = lines) giving the
local index of the B-element of the target.  R = set of freed local A-indices.

brute_bad(): counts ordered pairs (u in source level, v in target level) with no path of length <= 5 inside the two
levels; uses only distances in the incidence graph and the fact that a path of length <= 5 uses exactly one matching
edge (Lemma 3.1).  exact_conditions(): checks (E1), (E2), (E3) of Theorem E directly.
"""
import numpy as np


def full_dist(G):
    n, m = G.np, G.nl
    D = np.zeros((n + m, n + m), dtype=np.int8)
    D[:n, :n] = G.dpp; D[n:, n:] = G.dll; D[:n, n:] = G.dpl; D[n:, :n] = G.dpl.T
    return D


def ids(G, kind):
    return np.arange(G.np) if kind == 'P' else G.np + np.arange(G.nl)


def kinds(tj, tj2):
    ka = 'P' if tj == 'H' else 'L'
    kb2 = 'L' if tj2 == 'H' else 'P'
    return ka, kb2


def brute_bad(G, tj, tj2, M, R, D=None):
    """number of ordered pairs at distance > 5 within the two levels (counted over all 2N x 2N pairs)"""
    D = full_dist(G) if D is None else D
    ka, kb2 = kinds(tj, tj2)
    A = ids(G, ka); B2 = ids(G, kb2)
    keep = np.array([a for a in range(len(A)) if a not in R])
    src = A[keep]                      # element ids in source level
    dst = B2[np.asarray(M)[keep]]      # matched element ids in target level
    Du = D[:, src].astype(np.float32)  # (2N, k)
    Dv = D[dst, :].astype(np.float32)  # (k, 2N)
    ok = np.zeros((D.shape[0], D.shape[0]), dtype=bool)
    for d1 in range(5):
        left = (Du == d1).astype(np.float32)
        right = (Dv <= 4 - d1).astype(np.float32)
        ok |= (left @ right) > 0
    return int((~ok).sum())


def exact_conditions(G, tj, tj2, M, R):
    """(E1): not both: some B(source) element has all its incident elements in R, and some A(target) element has all
    its incident elements in M(R).
    (E2): for x in R, {M(a): a in Gamma2(x) minus R} covers A(target) (each A(target) element incident with one).
    (E3): for x in R, {a not in R: M(a) in Gamma2(M(x))} covers B(source).
    Returns (ok, list of failures)."""
    ka, kb2 = kinds(tj, tj2)
    M = np.asarray(M)
    R = set(R)
    # incidence matrices: inc_src[a, b] for A(source) x B(source); inc_dst[b2, a2] for B(target) x A(target)
    I = G.I.astype(bool)                # points x lines
    inc_src = I if ka == 'P' else I.T   # A(source) x B(source)
    inc_dst = I.T if kb2 == 'L' else I  # B(target) x A(target)
    g2_src = G.col if ka == 'P' else G.con
    g2_dst = G.con if kb2 == 'L' else G.col
    fails = []
    MR = np.zeros(len(M), dtype=bool)
    Rl = sorted(R)
    if Rl:
        MR[M[Rl]] = True
    # (E1): fails only if some B(source) element has all its neighbours in R AND some A(target) element has all its
    # neighbours in M(R)  (then that pair has no path of length <= 5 inside the two levels)
    cnt = inc_dst.astype(np.int32).T @ MR.astype(np.int32)      # for each A(target) element: # incident in M(R)
    deg = inc_dst.sum(axis=0)
    Rmask = np.zeros(len(M), dtype=bool)
    if Rl:
        Rmask[Rl] = True
    cntR = inc_src.astype(np.int32).T @ Rmask.astype(np.int32)  # for each B(source) element: # incident in R
    degR = inc_src.sum(axis=0)
    if (cnt >= deg).any() and (cntR >= degR).any():
        fails.append(('E1', int((cnt >= deg).sum()), int((cntR >= degR).sum())))
    notR = np.ones(len(M), dtype=bool)
    if Rl:
        notR[Rl] = False
    Minv = np.empty_like(M); Minv[M] = np.arange(len(M))
    for x in Rl:
        a_set = np.nonzero(g2_src[x] & notR)[0]
        cover = inc_dst[M[a_set]].any(axis=0)
        if not cover.all():
            fails.append(('E2', x, int((~cover).sum())))
        b_set = np.nonzero(g2_dst[M[x]])[0]
        a2 = Minv[b_set]; a2 = a2[notR[a2]]
        cover2 = inc_src[a2].any(axis=0)
        if not cover2.all():
            fails.append(('E3', x, int((~cover2).sum())))
    return (not fails), fails
