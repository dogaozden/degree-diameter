#!/usr/bin/env python3
"""c7: build the actual lift for a chart and a controller (G, S) and verify it directly.

Vertices: A-side (g,x) -> g*729 + x ;  B-side (h,y) -> m*729 + h*729 + y ; x,y in F_3^6 (base-3 index).
Edges: (g,x)_A ~ (s_t g, A_t x + lam b_t)_B for t in 0..4, lam in F_3 (15 neighbours).

Checks: simple, 15-regular, both sides define the same edge set (symmetry), and diameter <= 7.
Diameter check is EXACT in FULL mode: right multiplication by G is an automorphism (transitive on g), so the
eccentricity of (g,x)_A equals that of (e,x)_A; sources (e,x)_A and (e,y)_B for all 729+729 fibre points suffice.

Usage: python3 verify_lift.py CHART.npz SPEC S0,S1,S2,S3,S4 MODE [SAMPLES SEED]   (MODE = full | sample)
"""
import numpy as np, sys, itertools, time
import cover

POW = 3 ** np.arange(6)


def enc(V):
    return (V % 3) @ POW


def main():
    chart_path, spec, Sstr, mode = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    samples = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    d = np.load(chart_path)
    A, Ainv, b = d["A"].astype(np.int64), d["Ainv"].astype(np.int64), d["b"].astype(np.int64)
    G, name = cover.build(spec)
    mul, e, inv = G
    m = mul.shape[0]
    S = np.array([int(x) for x in Sstr.split(",")], dtype=np.int64)
    assert len(set(S.tolist())) == 5 and (A % 3 == A).all()
    X = np.array([[(r // 3 ** i) % 3 for i in range(6)] for r in range(729)], dtype=np.int64)
    assert (enc(X) == np.arange(729)).all()
    M = m * 729
    N = 2 * M
    adj = np.empty((N, 15), dtype=np.int64)
    ar = np.arange(m)
    for t in range(5):
        for lam in range(3):
            k = 3 * t + lam
            yA = enc(X @ A[t].T + lam * b[t])                  # A -> B fibre map
            hB = mul[S[t], ar]                                 # s_t g
            adj[:M, k] = (M + hB[:, None] * 729 + yA[None, :]).ravel()
            xB = enc((X - lam * b[t]) @ Ainv[t].T)             # B -> A fibre map (inverse)
            gA = mul[inv[S[t]], ar]                            # s_t^{-1} h
            adj[M:, k] = (gA[:, None] * 729 + xB[None, :]).ravel()
    srt = np.sort(adj, axis=1)
    simple = bool((np.diff(srt, axis=1) != 0).all())
    del srt
    cA = np.sort(np.repeat(np.arange(M, dtype=np.int64), 15) * N + adj[:M].ravel())
    cB = np.sort(adj[M:].ravel() * N + np.repeat(np.arange(M, N, dtype=np.int64), 15))
    symmetric = bool(np.array_equal(cA, cB))
    del cA, cB
    print(f"{name} m={m} N={N} simple={simple} symmetric={symmetric}", flush=True)

    def bfs(s):
        dist = np.full(N, -1, dtype=np.int32)
        dist[s] = 0
        fr = np.array([s], dtype=np.int64)
        dd = 0
        while fr.size:
            nb = adj[fr].ravel()
            nb = nb[dist[nb] < 0]
            if nb.size == 0:
                break
            dd += 1
            dist[nb] = dd
            fr = np.flatnonzero(dist == dd)
        return dist

    if mode == "full":
        srcs = [e * 729 + x for x in range(729)] + [M + e * 729 + y for y in range(729)]
    else:
        rng = np.random.default_rng(seed)
        srcs = [e * 729, M + e * 729] + [int(v) for v in rng.integers(0, M, samples)] + \
               [int(M + v) for v in rng.integers(0, M, samples)]
    worst = 0
    allreached = True
    t0 = time.time()
    for i, s in enumerate(srcs):
        dist = bfs(s)
        if (dist < 0).any():
            allreached = False
        worst = max(worst, int(dist.max()))
        if i in (0, 9, 99, 399, 799, 1199) or i == len(srcs) - 1:
            print(f"  after {i+1} sources: max ecc {worst}, {time.time()-t0:.1f}s", flush=True)
    print(f"BFS sources={len(srcs)} ({mode}): max eccentricity {worst}, all reached {allreached}, "
          f"{time.time()-t0:.1f}s", flush=True)
    ok = simple and symmetric and allreached and worst <= 7
    print("RESULT", "PASS" if ok else "FAIL", f"N={N}", flush=True)


if __name__ == "__main__":
    main()
