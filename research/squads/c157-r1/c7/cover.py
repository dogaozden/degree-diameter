#!/usr/bin/env python3
"""c7: does a controller group G with 5-set S cover G by nonsingular NB-6 words?

Controller Haar graph H(G,S): A-vertex g ~ B-vertex s_t g.  Walks from e (letters t1..t6, t_i != t_{i+1}):
  start A (steps F,G,F,G,F,G):  W_A(P) = s_t6^-1 s_t5 s_t4^-1 s_t3 s_t2^-1 s_t1
  start B (steps G,F,G,F,G,F):  W_B(P) = s_t6 s_t5^-1 s_t4 s_t3^-1 s_t2 s_t1^-1
A perfect controller needs {W_A(P): P in N_A} = G and {W_B(P): P in N_B} = G, where N_A, N_B are the
nonsingular pattern sets of the chart (chart.py). Then the (15,7) lift has diameter <= 7 (see README in REPORT).
Groups: Z{m}, PSL{p}, SL{p}, PGL{p} (p prime), optionally times Z{n} written as ...x{n}.

Usage: python3 cover.py CHART.npz OUT.jsonl TRIES LS_STEPS SEED SPEC [SPEC ...]
"""
import numpy as np, sys, os, json, time, re


def finish(mul, e):
    mul = np.asarray(mul, dtype=np.int64)
    inv = np.argmax(mul == e, axis=1).astype(np.int64)
    return mul, int(e), inv


def check_group(G, rng, trials=2000):
    mul, e, inv = G
    m = mul.shape[0]
    assert (mul[e] == np.arange(m)).all() and (mul[:, e] == np.arange(m)).all()
    assert all(np.unique(mul[g]).size == m for g in range(0, m, max(1, m // 50)))
    a, b, c = rng.integers(m, size=(3, trials))
    assert (mul[mul[a, b], c] == mul[a, mul[b, c]]).all(), "associativity failed"
    assert (mul[inv, np.arange(m)] == e).all()
    return True


def cyclic(m):
    ar = np.arange(m)
    return finish((ar[:, None] + ar[None, :]) % m, 0), f"Z{m}"


def mat_group(p, kind):
    idx = np.arange(p ** 4)
    a = idx // p ** 3
    b = (idx // p ** 2) % p
    c = (idx // p) % p
    d = idx % p
    det = (a * d - b * c) % p
    first = np.where(a != 0, a, np.where(b != 0, b, np.where(c != 0, c, d)))
    neg = ((-a) % p) * p ** 3 + ((-b) % p) * p ** 2 + ((-c) % p) * p + ((-d) % p)
    if kind == 'SL':
        keep = det == 1
    elif kind == 'PSL':
        keep = (det == 1) & (idx <= neg)
    elif kind == 'PGL':
        keep = (det != 0) & (first == 1)
    else:
        raise ValueError(kind)
    E = np.stack([a[keep], b[keep], c[keep], d[keep]], axis=1)
    m = E.shape[0]
    lookup = -np.ones(p ** 4, dtype=np.int64)
    lookup[idx[keep]] = np.arange(m)
    invt = np.array([0] + [pow(v, p - 2, p) for v in range(1, p)], dtype=np.int64)

    def canon_index(X):
        x = X % p
        if kind == 'SL':
            codes = x[:, 0] * p ** 3 + x[:, 1] * p ** 2 + x[:, 2] * p + x[:, 3]
        elif kind == 'PSL':
            nx = (-x) % p
            c1 = x[:, 0] * p ** 3 + x[:, 1] * p ** 2 + x[:, 2] * p + x[:, 3]
            c2 = nx[:, 0] * p ** 3 + nx[:, 1] * p ** 2 + nx[:, 2] * p + nx[:, 3]
            codes = np.minimum(c1, c2)
        else:
            fz = np.where(x[:, 0] != 0, x[:, 0], np.where(x[:, 1] != 0, x[:, 1],
                          np.where(x[:, 2] != 0, x[:, 2], x[:, 3])))
            y = (x * invt[fz][:, None]) % p
            codes = y[:, 0] * p ** 3 + y[:, 1] * p ** 2 + y[:, 2] * p + y[:, 3]
        ix = lookup[codes]
        assert (ix >= 0).all()
        return ix

    mul = np.empty((m, m), dtype=np.int64)
    A2, B2, C2, D2 = E[:, 0], E[:, 1], E[:, 2], E[:, 3]
    for i in range(m):
        A1, B1, C1, D1 = E[i]
        X = np.stack([A1 * A2 + B1 * C2, A1 * B2 + B1 * D2, C1 * A2 + D1 * C2, C1 * B2 + D1 * D2], axis=1)
        mul[i] = canon_index(X)
    e = int(canon_index(np.array([[1, 0, 0, 1]]))[0])
    return finish(mul, e), f"{kind}({p})"


def times_cyclic(G, name, n):
    mul0, e0, _ = G
    m0 = mul0.shape[0]
    N = m0 * n
    I = np.arange(N) // n
    K = np.arange(N) % n
    mul = mul0[I[:, None], I[None, :]] * n + (K[:, None] + K[None, :]) % n
    return finish(mul, e0 * n), f"{name}x Z{n}"


def build(spec):
    m_ = re.fullmatch(r"Z(\d+)", spec)
    if m_:
        return cyclic(int(m_.group(1)))
    m_ = re.fullmatch(r"(PSL|SL|PGL)(\d+)(?:x(\d+))?", spec)
    if not m_:
        raise ValueError(spec)
    G, name = mat_group(int(m_.group(2)), m_.group(1))
    if m_.group(3):
        G, name = times_cyclic(G, name, int(m_.group(3)))
    return G, name


def word_elems(G, S, P, start):
    mul, e, inv = G
    types = (0, 1, 0, 1, 0, 1) if start == 'A' else (1, 0, 1, 0, 1, 0)  # 0 = F (A->B), 1 = G (B->A)
    cur = np.full(P.shape[0], e, dtype=np.int64)
    for i in range(6):
        gens = S[P[:, i]]
        cur = mul[gens, cur] if types[i] == 0 else mul[inv[gens], cur]
    return cur


def coverage(G, S, P, mA, mB):
    cA = np.unique(word_elems(G, S, P, 'A')[mA]).size
    cB = np.unique(word_elems(G, S, P, 'B')[mB]).size
    return int(cA), int(cB)


def run_group(spec, chart, tries, ls_steps, seed, out):
    rng = np.random.default_rng(seed)
    G, name = build(spec)
    check_group(G, rng)
    m = G[0].shape[0]
    P, mA, mB = chart['P'], chart['mA'], chart['mB']
    t0 = time.time()
    n_full = 0
    best = None
    maxA = maxB = 0
    for _ in range(tries):
        S = rng.choice(m, 5, replace=False)
        cA, cB = coverage(G, S, P, mA, mB)
        maxA, maxB = max(maxA, cA), max(maxB, cB)
        if cA == m and cB == m:
            n_full += 1
        if best is None or cA + cB > best[0]:
            best = (cA + cB, S.copy(), cA, cB)
    # local search on S (swap one generator), maximising covered A + B counts
    cur, S, cA, cB = best[0], best[1].copy(), best[2], best[3]
    for _ in range(ls_steps):
        if cA == m and cB == m:
            break
        j = int(rng.integers(5))
        new = int(rng.integers(m))
        if new in S:
            continue
        S2 = S.copy()
        S2[j] = new
        a2, b2 = coverage(G, S2, P, mA, mB)
        if a2 + b2 >= cur:
            S, cur, cA, cB = S2, a2 + b2, a2, b2
    full_ls = (cA == m and cB == m)
    rec = {"group": name, "m": int(m), "random_tries": tries, "random_full_covers": int(n_full),
           "random_max_covered_A": int(maxA), "random_max_covered_B": int(maxB),
           "ls_best_covered_A": int(cA), "ls_best_covered_B": int(cB),
           "full_cover_found": bool(n_full > 0 or full_ls), "S": [int(x) for x in S],
           "seconds": round(time.time() - t0, 1)}
    print(json.dumps(rec), flush=True)
    with open(out, "a") as f:
        f.write(json.dumps(rec) + "\n")
    return rec


def main():
    chart_path, out, tries, ls_steps, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    d = np.load(chart_path)
    chart = {"P": d["patterns"].astype(np.int64), "mA": d["maskA"].astype(bool), "mB": d["maskB"].astype(bool)}
    print(f"chart nonsingular: A {chart['mA'].sum()}/5120  B {chart['mB'].sum()}/5120", flush=True)
    for k, spec in enumerate(sys.argv[6:]):
        run_group(spec, chart, tries, ls_steps, seed + k, out)


if __name__ == "__main__":
    main()
