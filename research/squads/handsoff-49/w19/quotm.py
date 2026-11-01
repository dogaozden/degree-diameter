#!/usr/bin/env python3
"""w19: normal quotients of many Haar graphs H(G,S) of one meta group G = Z_m x|_r Z_k (index a + m*j).
Usage: quotm.py m k r HITS OUTDIR KSUB [maxS]
  HITS: lines "cost s1 s2 s3 s4" (indices a+m*j, identity 0 allowed, as in w11/hits).
  KSUB: the index of the normal subgroup K (contains G') of G, i.e. base size 2*KSUB.
Writes OUTDIR/K<idx>.bin (group table of K, identity 0, shared by all S), OUTDIR/S<i>.base ("b m" then "u v g"
lines, the Haar voltages over K) and OUTDIR/index.tsv (i, hit cost, base file). Lift = flift/lann convention."""
import sys, os
import numpy as np

def group(m, k, r):
    N = m * k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N); A = idx % m; J = idx // m
    T = (((A[:, None] + rp[J][:, None] * A[None, :]) % m) + m * ((J[:, None] + J[None, :]) % k)).astype(np.int64)
    INV = np.array([int(np.where(T[g] == 0)[0][0]) for g in range(N)])
    return N, T, INV

def closure(T, gs, N):
    seen = {0}; frontier = [0]
    while frontier:
        nf = []
        for x in frontier:
            for g in gs:
                y = int(T[x, g])
                if y not in seen: seen.add(y); nf.append(y)
        frontier = nf
    return seen

def main():
    m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    hits = sys.argv[4]; out = sys.argv[5]; ksub = int(sys.argv[6])
    maxS = int(sys.argv[7]) if len(sys.argv) > 7 else 10**9
    os.makedirs(out, exist_ok=True)
    N, T, INV = group(m, k, r)
    idx = np.arange(N)
    comm = T[T[np.repeat(idx, N), np.tile(idx, N)], np.zeros(N * N, dtype=np.int64)]  # placeholder, replaced below
    X = np.repeat(idx, N); Y = np.tile(idx, N)
    comm = T[T[X, Y], T[INV[X], INV[Y]]]
    Gp = sorted(closure(T, list(np.unique(comm)), N))
    cid = -np.ones(N, dtype=np.int64); reps = []
    for g in range(N):
        if cid[g] < 0:
            c = len(reps); reps.append(g)
            for h in Gp: cid[int(T[g, h])] = c
    Q = len(reps)
    QT = np.array([[cid[int(T[reps[a], reps[b]])] for b in range(Q)] for a in range(Q)])
    def qclose(gs):
        seen = {0}; frontier = [0]
        while frontier:
            nf = []
            for x in frontier:
                for g in gs:
                    y = int(QT[x, g])
                    if y not in seen: seen.add(y); nf.append(y)
            frontier = nf
        return frozenset(seen)
    subs = {qclose([])}
    for a in range(Q): subs.add(qclose([a]))
    for a in range(Q):
        for b in range(a + 1, Q): subs.add(qclose([a, b]))
    cands = [H for H in subs if Q // len(H) == ksub]
    if not cands:
        print("no normal subgroup of index", ksub); return
    H = sorted(cands, key=lambda s: sorted(s))[0]
    Kel = sorted(int(g) for g in range(N) if int(cid[g]) in H)
    Kel.remove(0); Kel = [0] + Kel
    Ksz = len(Kel); pos = {g: i for i, g in enumerate(Kel)}
    KT = np.zeros((Ksz, Ksz), dtype=np.uint16)
    for i, g in enumerate(Kel):
        for j, h in enumerate(Kel): KT[i, j] = pos[int(T[g, h])]
    with open(os.path.join(out, "K.bin"), "wb") as f:
        np.array([Ksz], dtype=np.int32).tofile(f); KT.tofile(f)
    kc = -np.ones(N, dtype=np.int64); kreps = []
    for g in range(N):
        if kc[g] < 0:
            c = len(kreps); kreps.append(g)
            for h in Kel: kc[int(T[g, h])] = c
    kk = len(kreps)
    tsv = open(os.path.join(out, "index.tsv"), "w")
    cnt = 0
    for line in open(hits):
        p = line.split()
        if len(p) < 5: continue
        if cnt >= maxS: break
        cost = int(p[0]); S = [int(x) for x in p[1:5]]
        edges = []
        for c in range(kk):
            rc = kreps[c]
            for s in S:
                x = int(T[s, rc]); c2 = int(kc[x])
                t = int(T[INV[kreps[c2]], x])
                assert int(kc[t]) == 0 and t in pos
                edges.append((c, kk + c2, pos[t]))
        fn = f"S{cnt}.base"
        with open(os.path.join(out, fn), "w") as f:
            f.write(f"{2*kk} {len(edges)}\n")
            for u, v, g in edges: f.write(f"{u} {v} {g}\n")
        tsv.write(f"{cnt}\t{cost}\t{fn}\t{p[1:5]}\n")
        cnt += 1
    tsv.close()
    print(f"K order {Ksz}, index {kk}, base {2*kk}+{2*kk}-vertices, wrote {cnt} bases to {out}")

if __name__ == "__main__":
    main()
