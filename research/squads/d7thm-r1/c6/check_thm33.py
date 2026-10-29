#!/usr/bin/env python3
"""Card c6 (squad d7thm-r1): independent check of Theorem 3.3 in D7_THEOREMS.md.

Setting: L = 2k+1 levels, a regular tournament (out- and in-degree k), each level typed H or D.
Arc i->j has weight P if friendly (types differ) and type(i)=H, Lam if friendly and type(i)=D, m if not friendly.
alpha_i = out-weight sum of i, beta_j = in-weight sum of j.

Families:
  E5, E7   all labelled regular tournaments on 5 / 7 levels (backtracking) x all 2^L typings
  R9, R11  200,000 random regular tournaments each (walk of directed 3-cycle reversals), one random typing each
  Rot9, Rot11  rotational tournament x all 2^L typings
  C2       rotational tournament with alternating typing, k = 1..40: exact values of min alpha, min beta
  C3       closed form for f_i and the in-count identity, k = 1..40

Claim (1): k even: min alpha <= a(Lam+m), min beta <= a(Lam+m), a = k/2.
           k odd : min alpha + min beta <= a(P+Lam)+(k+1)m and each min <= aP+(a+1)m, a = (k-1)/2.
Claim (2): k even: min alpha = min beta = a(Lam+m) for rotational + alternating typing.
           k odd : min alpha = aP+(a+1)m, min beta = a*Lam+(a+1)m.
Claim (3): closed form for f_i (friendly out-count), and g_i (friendly in-count) = f_{2k-i}.
"""
import os
import random
import sys
import time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def q_triple(q):
    return ((q + 1) * (q ** 3 + 1), q ** 4 + q ** 2 + q, q ** 2 + 1)


PARAMS = []
for q in (11, 13, 16, 101):
    P, Lam, m = q_triple(q)
    PARAMS.append(("q%d" % q, P, Lam, m))
PARAMS.append(("x15984", 15984, 14773, 768))
PARAMS.append(("x30772", 30772, 28743, 792))
for name, P, Lam, m in PARAMS:
    assert P > Lam > m > 0, name

RES = {}
COUNTER = {"naive_checked": 0, "naive_mismatch": 0}


def rotational(L):
    k = (L - 1) // 2
    A = np.zeros((L, L), dtype=bool)
    for i in range(L):
        for t in range(1, k + 1):
            A[i, (i + t) % L] = True
    return A


def eval_counts(A, T):
    """A: (N,L,L) bool, A[n,i,j] iff arc i->j. T: (N,S,L) bool, True = type H.
    Returns per-vertex weight-class counts for out-arcs (a*) and in-arcs (b*)."""
    Ti = T[:, :, :, None]
    F = Ti != T[:, :, None, :]          # friendly[i,j]
    An = A[:, None, :, :]
    tH = np.broadcast_to(Ti, F.shape)   # tail type H
    frH = An & F & tH
    frD = An & F & ~tH
    unf = An & ~F
    return {
        "aP": frH.sum(axis=3), "aL": frD.sum(axis=3), "am": unf.sum(axis=3),
        "bP": frH.sum(axis=2), "bL": frD.sum(axis=2), "bm": unf.sum(axis=2),
    }


def min_alpha_beta(c, P, Lam, m):
    alpha = c["aP"] * P + c["aL"] * Lam + c["am"] * m
    beta = c["bP"] * P + c["bL"] * Lam + c["bm"] * m
    return alpha.min(axis=2), beta.min(axis=2), alpha, beta


def bounds(k, P, Lam, m):
    """returns (bA, bB, bS): bounds for min alpha, min beta, and the sum (None for k even)."""
    if k % 2 == 0:
        a = k // 2
        return a * (Lam + m), a * (Lam + m), None
    a = (k - 1) // 2
    return a * P + (a + 1) * m, a * P + (a + 1) * m, a * (P + Lam) + (k + 1) * m


def naive_minmax(Al, Tl, P, Lam, m):
    """Straight-from-the-definition evaluator, used only as a cross-check."""
    L = len(Al)
    alpha = [0] * L
    beta = [0] * L
    for i in range(L):
        for j in range(L):
            if Al[i][j]:
                if Tl[i] != Tl[j]:
                    w = P if Tl[i] else Lam
                else:
                    w = m
                alpha[i] += w
                beta[j] += w
    return min(alpha), min(beta)


def tally_batch(family, k, A, T, naive_samples=150, rng=None):
    """Checks claim (1) on every (tournament, typing) in the batch for all parameter sets."""
    N, S = T.shape[0], T.shape[1]
    c = eval_counts(A, T)
    rng = rng or random.Random(0)
    picks = [(rng.randrange(N), rng.randrange(S)) for _ in range(min(naive_samples, N * S))]
    for pname, P, Lam, m in PARAMS:
        minA, minB, _, _ = min_alpha_beta(c, P, Lam, m)
        bA, bB, bS = bounds(k, P, Lam, m)
        mA = minA - bA
        mB = minB - bB
        r = RES.setdefault((family, pname), {
            "cases": 0, "failA": 0, "failB": 0, "failS": 0, "maxA": None, "maxB": None,
            "maxS": None, "ex": [], "k": k})
        r["cases"] += N * S
        r["failA"] += int((mA > 0).sum())
        r["failB"] += int((mB > 0).sum())
        r["maxA"] = int(mA.max()) if r["maxA"] is None else max(r["maxA"], int(mA.max()))
        r["maxB"] = int(mB.max()) if r["maxB"] is None else max(r["maxB"], int(mB.max()))
        if bS is not None:
            mS = (minA + minB) - bS
            r["failS"] += int((mS > 0).sum())
            r["maxS"] = int(mS.max()) if r["maxS"] is None else max(r["maxS"], int(mS.max()))
            bad = (mA > 0) | (mB > 0) | (mS > 0)
        else:
            bad = (mA > 0) | (mB > 0)
        if bad.any() and len(r["ex"]) < 3:
            for n, s in np.argwhere(bad)[:3]:
                if len(r["ex"]) >= 3:
                    break
                r["ex"].append({
                    "arcs_adj": A[n].astype(int).tolist(),
                    "H_types": T[n, s].astype(int).tolist(),
                    "minA": int(minA[n, s]), "minB": int(minB[n, s]),
                    "bA": bA, "bB": bB, "bS": bS})
        # cross-check the vectorised evaluator against the naive one
        for (n, s) in picks:
            nA, nB = naive_minmax(A[n].astype(int).tolist(), T[n, s].astype(int).tolist(), P, Lam, m)
            COUNTER["naive_checked"] += 1
            if nA != int(minA[n, s]) or nB != int(minB[n, s]):
                COUNTER["naive_mismatch"] += 1


def walk_batches(L, total, batch, seed, spacing=20, burn=5000):
    """Random regular tournaments: walk of directed 3-cycle reversals starting from the rotational one.
    Each reversal of i->j->c->i to j->i, c->j, i->c keeps every out- and in-degree equal to k."""
    rng = random.Random(seed)
    A = [[1 if 1 <= (j - i) % L <= (L - 1) // 2 else 0 for j in range(L)] for i in range(L)]

    def step():
        i = rng.randrange(L)
        j = rng.randrange(L)
        c = rng.randrange(L)
        if i == j or j == c or c == i:
            return
        if A[i][j] and A[j][c] and A[c][i]:
            A[i][j] = A[j][c] = A[c][i] = 0
            A[j][i] = A[c][j] = A[i][c] = 1

    for _ in range(burn):
        step()
    buf = []
    for _ in range(total):
        for _ in range(spacing):
            step()
        buf.append(np.array(A, dtype=bool))
        if len(buf) == batch:
            yield np.stack(buf)
            buf = []
    if buf:
        yield np.stack(buf)


def enum_regular(L):
    """All labelled regular tournaments on L = 2k+1 vertices (out-degree k), by backtracking over pairs."""
    k = (L - 1) // 2
    pairs = [(i, j) for i in range(L) for j in range(i + 1, L)]
    out = [0] * L
    inn = [0] * L
    A = [[0] * L for _ in range(L)]
    res = []

    def rec(p):
        if p == len(pairs):
            if all(o == k for o in out) and all(x == k for x in inn):
                res.append(np.array(A, dtype=bool))
            return
        i, j = pairs[p]
        if out[i] < k and inn[j] < k:
            out[i] += 1; inn[j] += 1; A[i][j] = 1
            rec(p + 1)
            out[i] -= 1; inn[j] -= 1; A[i][j] = 0
        if out[j] < k and inn[i] < k:
            out[j] += 1; inn[i] += 1; A[j][i] = 1
            rec(p + 1)
            out[j] -= 1; inn[i] -= 1; A[j][i] = 0

    rec(0)
    return np.stack(res)


def all_typings(L):
    idx = np.arange(2 ** L)
    return ((idx[:, None] >> np.arange(L)[None, :]) & 1).astype(bool)  # (2^L, L), True = H


def f_closed(k, i):
    """Claim (3): friendly out-count of level i in the rotational/alternating construction."""
    if i <= k:
        return (k + 1) // 2
    t = i - k
    if k % 2 == 0:
        return k // 2 if t % 2 == 0 else k // 2 + 1
    return (k - 1) // 2 if t % 2 == 1 else (k + 1) // 2


def main():
    t0 = time.time()
    log = []

    def say(s):
        print(s)
        sys.stdout.flush()

    say("parameter sets:")
    for name, P, Lam, m in PARAMS:
        say("  %-8s P=%d Lam=%d m=%d" % (name, P, Lam, m))

    # ---- (a) exhaustive on 5 and 7 levels ----
    for L in (3, 5, 7):
        k = (L - 1) // 2
        Ts = enum_regular(L)
        say("L=%d: labelled regular tournaments enumerated: %d" % (L, len(Ts)))
        Tall = all_typings(L)
        S = Tall.shape[0]
        chunk = max(1, 200000 // S)
        for st in range(0, len(Ts), chunk):
            A = Ts[st:st + chunk]
            T = np.broadcast_to(Tall[None], (A.shape[0], S, L))
            tally_batch("E%d" % L, k, A, T)
        say("  E%d done, cases per param set = %d x %d" % (L, len(Ts), S))

    # ---- (b) random tournaments on 9 and 11 levels, random typing each ----
    NSAMP = 200000
    for L in (9, 11):
        k = (L - 1) // 2
        rng_np = np.random.default_rng(1000 + L)
        distinct = set()
        rng_py = random.Random(7 + L)
        seen = 0
        t1 = time.time()
        for batch in walk_batches(L, NSAMP, 20000, seed=L * 31 + 5):
            n = batch.shape[0]
            # regularity and tournament sanity
            assert (batch.sum(axis=2) == k).all() and (batch.sum(axis=1) == k).all()
            eye = np.eye(L, dtype=bool)
            assert ((batch | batch.transpose(0, 2, 1)) | eye).all()
            assert not (batch & batch.transpose(0, 2, 1)).any()
            for n_ in range(n):
                distinct.add(batch[n_].tobytes())
            T = (rng_np.random((n, 1, L)) < 0.5)
            tally_batch("R%d" % L, k, batch, T, naive_samples=60, rng=rng_py)
            seen += n
        say("R%d: %d random regular tournaments, %d distinct, one random typing each (%.1fs)"
            % (L, seen, len(distinct), time.time() - t1))

    # ---- (c) rotational tournament, all typings, 9 and 11 levels ----
    for L in (9, 11):
        k = (L - 1) // 2
        A = rotational(L)[None]
        Tall = all_typings(L)
        T = Tall[None]
        tally_batch("Rot%d" % L, k, A, T, naive_samples=300, rng=random.Random(3))
        say("Rot%d: rotational x %d typings done" % (L, Tall.shape[0]))

    # ---- (d) claim (2) and (3) for k = 1..40 ----
    c2_detail = {}
    c3_fail = []
    for k in range(1, 41):
        L = 2 * k + 1
        A = rotational(L)[None]
        T = np.array([[i % 2 == 0 for i in range(L)]], dtype=bool)[None]
        c = eval_counts(A, T)
        f = (c["aP"] + c["aL"])[0, 0]
        g = (c["bP"] + c["bL"])[0, 0]
        fc_ok = all(int(f[i]) == f_closed(k, i) for i in range(L))
        g_ok = all(int(g[i]) == int(f[2 * k - i]) for i in range(L))
        if not (fc_ok and g_ok):
            c3_fail.append(k)
        for pname, P, Lam, m in PARAMS:
            minA, minB, alpha, beta = min_alpha_beta(c, P, Lam, m)
            minA = int(minA[0, 0])
            minB = int(minB[0, 0])
            bA, bB, _ = bounds(k, P, Lam, m)
            if k % 2 == 0:
                eA, eB = bA, bB
            else:
                a = (k - 1) // 2
                eA, eB = a * P + (a + 1) * m, a * Lam + (a + 1) * m
            ok = (minA == eA and minB == eB)
            nA, nB = naive_minmax(rotational(L).astype(int).tolist(),
                                  [i % 2 == 0 for i in range(L)], P, Lam, m)
            COUNTER["naive_checked"] += 1
            if (nA, nB) != (minA, minB):
                COUNTER["naive_mismatch"] += 1
            d = c2_detail.setdefault(pname, {"pass": [], "fail": []})
            (d["pass"] if ok else d["fail"]).append(k)
            if not ok:
                # which vertex types realise the minimum
                aw = np.array(alpha[0, 0]); bw = np.array(beta[0, 0])
                ta = sorted(set("H" if i % 2 == 0 else "D" for i in np.flatnonzero(aw == minA)))
                tb = sorted(set("H" if i % 2 == 0 else "D" for i in np.flatnonzero(bw == minB)))
                c2_detail[pname].setdefault("why", []).append(
                    (k, minA, eA, ta, minB, eB, tb))
    say("C3 closed form for f_i and g_i = f_{2k-i}, k=1..40: %s" %
        ("ALL PASS" if not c3_fail else "FAIL at k=%s" % c3_fail))

    # ---- report ----
    say("")
    say("Claim (1) tallies (family, params): cases, failures of min alpha / min beta / sum, max margins (<=0 holds)")
    for key in sorted(RES.keys(), key=lambda x: (x[0], x[1])):
        r = RES[key]
        say("  %-6s %-8s cases=%-8d failA=%d failB=%d failS=%s maxA=%d maxB=%d maxS=%s" % (
            key[0], key[1], r["cases"], r["failA"], r["failB"],
            ("%d" % r["failS"]) if r["maxS"] is not None else "n/a", r["maxA"], r["maxB"],
            ("%d" % r["maxS"]) if r["maxS"] is not None else "n/a"))
        for e in r["ex"][:1]:
            say("     counterexample: %s" % e)
    say("Cross-check vs naive evaluator: %d cases, %d mismatches" %
        (COUNTER["naive_checked"], COUNTER["naive_mismatch"]))

    say("")
    say("Claim (2) (rotational + alternating typing, exact values), k = 1..40:")
    for pname, P, Lam, m in PARAMS:
        d = c2_detail[pname]
        say("  %-8s pass k in %s" % (pname, d["pass"]))
        say("  %-8s FAIL k in %s" % (pname, d["fail"]))
        for w in d.get("why", [])[:4]:
            say("     k=%d: min alpha=%d (claim %d, realised by %s); min beta=%d (claim %d, realised by %s)" % w)
    say("")
    say("Claim (3) closed forms: %s" % ("pass for all k=1..40" if not c3_fail else "fail at %s" % c3_fail))
    say("elapsed %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
