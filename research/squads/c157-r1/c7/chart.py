#!/usr/bin/env python3
"""c7 route-chart for the (15,7) lift over controller Haar graph H(G,S), |S| = 5, fibre F_3^6.

Chart: A_t in GL(6,3), b_t in F_3^6 (letters t = 0..4).
Lift edges: (g,x)_A ~ (s_t g, A_t x + lam b_t)_B,  lam in F_3.
  F step (A->B):  x -> A_t x + lam b_t           (linear part A_t,      perturbation  b_t)
  G step (B->A):  y -> A_t^{-1}(y - lam b_t)     (linear part A_t^{-1}, perturbation -A_t^{-1} b_t)
Walk letters t1..t6 with t_i != t_{i+1} (controller nonbacktracking): 5*4^5 = 5120 patterns per start side.
Start A: steps F,G,F,G,F,G.  Start B: steps G,F,G,F,G,F.
Direction vectors v_i = Lin_6 ... Lin_{i+1} q_i (q_i = perturbation of step i). The reachable fibre set of a
pattern is the affine image of F_3^6 under lam -> sum lam_i v_i, i.e. ALL of F_3^6 iff det[v_1..v_6] != 0 mod 3.
Usage:
  python3 chart.py search SEED ITERS RESTARTS      (hill/anneal on single entries, writes chart_best.npz)
  python3 chart.py selftest                        (checks det criterion against brute-force lam enumeration)
"""
import numpy as np, sys, os, time, json, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
NL, DIM = 5, 6


def all_patterns():
    pats = []

    def rec(seq):
        if len(seq) == 6:
            pats.append(seq)
            return
        for t in range(NL):
            if not seq or t != seq[-1]:
                rec(seq + [t])
    rec([])
    return np.array(pats, dtype=np.int64)


PATS = all_patterns()  # (5120, 6)
assert PATS.shape == (5120, 6)


def inv_mod3(M):
    n = M.shape[0]
    A = np.concatenate([np.array(M, dtype=np.int64) % 3, np.eye(n, dtype=np.int64)], axis=1)
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, n):
            if A[i, c] % 3:
                piv = i
                break
        if piv is None:
            return None
        A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * (1 if A[r, c] == 1 else 2)) % 3
        for i in range(n):
            if i != r and A[i, c] % 3:
                A[i] = (A[i] - A[i, c] * A[r]) % 3
        r += 1
    return A[:, n:]


def det3(M):
    return int(round(np.linalg.det(np.array(M, dtype=float)))) % 3


def side_masks(A, Ainv, b):
    """Return (maskA, maskB): bool arrays over PATS for walks starting on side A / B."""
    out = []
    Abinv = (-np.einsum('tij,tj->ti', Ainv.astype(float), b.astype(float))) % 3  # -A_t^{-1} b_t
    for start in ('A', 'B'):
        types = [0, 1, 0, 1, 0, 1] if start == 'A' else [1, 0, 1, 0, 1, 0]  # 0=F, 1=G
        N = PATS.shape[0]
        Lin, Qv = [], []
        for i in range(6):
            t = PATS[:, i]
            if types[i] == 0:
                Lin.append(A[t])
                Qv.append(b[t].astype(float))
            else:
                Lin.append(Ainv[t])
                Qv.append(Abinv[t])
        Suf = [None] * 6
        Suf[5] = np.broadcast_to(np.eye(DIM), (N, DIM, DIM)).astype(float)
        for i in range(4, -1, -1):
            Suf[i] = np.matmul(Suf[i + 1], Lin[i + 1]) % 3
        V = np.empty((N, DIM, DIM))
        for i in range(6):
            V[:, :, i] = np.einsum('nij,nj->ni', Suf[i], Qv[i]) % 3
        d = np.rint(np.linalg.det(V)).astype(np.int64) % 3
        out.append(d != 0)
    return out[0], out[1]


def random_chart(rng):
    while True:
        A = rng.integers(0, 3, (NL, DIM, DIM))
        Ainv = np.zeros_like(A)
        ok = True
        for t in range(NL):
            iv = inv_mod3(A[t])
            if iv is None:
                ok = False
                break
            Ainv[t] = iv
        if ok:
            b = rng.integers(0, 3, (NL, DIM))
            if np.all(b.any(axis=1)):
                return A, Ainv, b


def score(A, Ainv, b):
    mA, mB = side_masks(A, Ainv, b)
    return int(mA.sum() + mB.sum()), mA, mB


def search(seed, iters, restarts, out_path):
    rng = np.random.default_rng(seed)
    best_overall = None
    for rs in range(restarts):
        A, Ainv, b = random_chart(rng)
        cur, mA, mB = score(A, Ainv, b)
        best = (cur, A.copy(), Ainv.copy(), b.copy(), mA.copy(), mB.copy())
        t0 = time.time()
        for it in range(iters):
            T = 6.0 * (1 - it / iters) + 0.3
            t = int(rng.integers(NL))
            if rng.random() < 0.8:
                i, j = int(rng.integers(DIM)), int(rng.integers(DIM))
                A2 = A.copy()
                A2[t, i, j] = (A[t, i, j] + int(rng.integers(1, 3))) % 3
                iv = inv_mod3(A2[t])
                if iv is None:
                    continue
                Ainv2 = Ainv.copy()
                Ainv2[t] = iv
                b2 = b
            else:
                j = int(rng.integers(DIM))
                b2 = b.copy()
                b2[t, j] = (b[t, j] + int(rng.integers(1, 3))) % 3
                if not b2[t].any():
                    continue
                A2, Ainv2 = A, Ainv
            new, nA, nB = score(A2, Ainv2, b2)
            if new >= cur or rng.random() < np.exp((new - cur) / T):
                A, Ainv, b, cur, mA, mB = A2, Ainv2, b2, new, nA, nB
                if cur > best[0]:
                    best = (cur, A.copy(), Ainv.copy(), b.copy(), mA.copy(), mB.copy())
        print(f"restart {rs}: best nonsingular {best[0]}/10240 = {best[0]/10240:.4f} "
              f"(A {best[4].sum()}, B {best[5].sum()}) time {time.time()-t0:.1f}s", flush=True)
        if best_overall is None or best[0] > best_overall[0]:
            best_overall = best
    cnt, A, Ainv, b, mA, mB = best_overall
    np.savez(out_path, A=A, Ainv=Ainv, b=b, maskA=mA, maskB=mB, patterns=PATS)
    print(json.dumps({"best_total": int(cnt), "fracA": float(mA.mean()), "fracB": float(mB.mean()),
                      "fraction_both": cnt / 10240}))


def selftest(seed=1):
    """Brute-force check: image of lam -> x6 has 3^6 points iff det criterion says nonsingular."""
    rng = np.random.default_rng(seed)
    A, Ainv, b = random_chart(rng)
    mA, mB = side_masks(A, Ainv, b)
    lams = np.array(list(itertools.product(range(3), repeat=6)))  # 729 x 6
    checked = agree = 0
    for idx in rng.choice(PATS.shape[0], 300, replace=False):
        for start, mask in (('A', mA), ('B', mB)):
            types = [0, 1, 0, 1, 0, 1] if start == 'A' else [1, 0, 1, 0, 1, 0]
            pts = np.zeros((729, 6), dtype=np.int64)  # start at x0 = 0 (linear image is what matters)
            for lam_idx in range(729):
                x = np.zeros(6, dtype=np.int64)
                for i in range(6):
                    t = PATS[idx, i]
                    lam = lams[lam_idx, i]
                    if types[i] == 0:
                        x = (A[t] @ x + lam * b[t]) % 3
                    else:
                        x = (Ainv[t] @ ((x - lam * b[t]) % 3)) % 3
                pts[lam_idx] = x
            image = len({tuple(p) for p in pts})
            crit = bool(mask[idx])
            checked += 1
            agree += int((image == 729) == crit)
    print(f"selftest: {agree}/{checked} patterns agree (brute-force full image vs det criterion)")
    return agree == checked


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "search":
        search(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), os.path.join(HERE, "chart_best.npz"))
    elif cmd == "selftest":
        ok = selftest(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
        sys.exit(0 if ok else 1)
