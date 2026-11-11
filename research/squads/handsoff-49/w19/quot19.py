#!/usr/bin/env python3
"""w19: normal quotients of Haar graphs H(G,S), G = meta m k r (index a + m*j, product (a,j)(b,l) = (a + r^j b, j+l)).
For every normal subgroup K containing G' (so G/K is abelian of order k), build the k+k base and the voltage
group table of K (identity = index 0, flift/wl2 convention: lift edge (u,x) ~ (v, g x)).
Usage: quot19.py m k r "a:j,a:j,a:j,a:j" OUTDIR [kmax]
Writes OUTDIR/K<idx>.bin (group table), OUTDIR/base<idx>.txt ("b m" then "u v g" lines, g = Haar voltage index in K),
and prints one line per subgroup: idx, |K|, k (index), base size, file names."""
import sys, os
import numpy as np

def main():
    m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    S = []
    for tok in sys.argv[4].split(","):
        a, j = tok.split(":"); S.append((int(a), int(j)))
    out = sys.argv[5]
    kmax = int(sys.argv[6]) if len(sys.argv) > 6 else 1000
    os.makedirs(out, exist_ok=True)
    N = m * k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N)
    A = idx % m; J = idx // m
    # T[x, y] = index of x*y
    T = (((A[:, None] + rp[J][:, None] * A[None, :]) % m) + m * ((J[:, None] + J[None, :]) % k)).astype(np.int64)
    INV = np.array([int(np.where(T[g] == 0)[0][0]) for g in range(N)])
    Sidx = [a + m * j for (a, j) in S]
    # commutator subgroup G' = <[x,y]>
    X = np.repeat(idx, N); Y = np.tile(idx, N)
    C = T[T[X, Y], np.zeros_like(X)]  # placeholder to keep shapes
    comm = T[T[X, Y], T[INV[X], INV[Y]]]
    gens = np.unique(comm)
    def closure(gs):
        seen = np.zeros(N, dtype=bool); seen[0] = True; frontier = [0]; elems = [0]
        while frontier:
            nf = []
            for x in frontier:
                for g in gs:
                    y = int(T[x, g])
                    if not seen[y]:
                        seen[y] = True; nf.append(y); elems.append(y)
            frontier = nf
        return sorted(elems)
    Gp = closure(list(gens))
    # cosets of G' (normal): cid over G
    cid = -np.ones(N, dtype=np.int64); reps = []
    for g in range(N):
        if cid[g] < 0:
            c = len(reps); reps.append(g)
            for h in Gp:
                cid[int(T[g, h])] = c
    Q = len(reps)
    QT = np.array([[cid[int(T[reps[a], reps[b]])] for b in range(Q)] for a in range(Q)])
    # subgroups of Q (abelian, order Q), by closure of up to 2 generators
    def qclose(gs):
        seen = {0}; frontier = [0]
        while frontier:
            nf = []
            for x in frontier:
                for g in gs:
                    y = int(QT[x, g])
                    if y not in seen:
                        seen.add(y); nf.append(y)
            frontier = nf
        return frozenset(seen)
    subs = set([qclose([])])
    for a in range(Q):
        subs.add(qclose([a]))
    for a in range(Q):
        for b in range(a + 1, Q):
            subs.add(qclose([a, b]))
    # every subgroup of an abelian group of rank <= 2 is 2-generated; close under 3-gens if needed
    subs = sorted(subs, key=lambda s: -len(s))
    idxk = 0
    for H in subs:
        Kidx_order = Q // len(H)  # index of K in G (= k of the base)
        if Kidx_order > kmax or Kidx_order < 1:
            continue
        Kel = sorted(int(g) for g in range(N) if int(cid[g]) in H)
        Kel.remove(0); Kel = [0] + Kel     # identity first
        Ksz = len(Kel)
        pos = {g: i for i, g in enumerate(Kel)}
        KT = np.zeros((Ksz, Ksz), dtype=np.uint16)
        for i, g in enumerate(Kel):
            for j, h in enumerate(Kel):
                KT[i, j] = pos[int(T[g, h])]
        # cosets of K in G (K normal): coset id by rep
        kc = -np.ones(N, dtype=np.int64); kreps = []
        for g in range(N):
            if kc[g] < 0:
                c = len(kreps); kreps.append(g)
                for h in Kel:
                    kc[int(T[g, h])] = c
        kk = len(kreps)
        assert kk == Kidx_order, (kk, Kidx_order)
        edges = []
        for c in range(kk):
            rc = kreps[c]
            for s in Sidx:
                x = int(T[s, rc]); c2 = int(kc[x])
                t = int(T[INV[kreps[c2]], x])
                assert int(kc[t]) == 0 and t in pos, "voltage not in K"
                edges.append((c, kk + c2, pos[t]))
        fn = os.path.join(out, f"K{idxk}")
        with open(fn + ".bin", "wb") as f:
            np.array([Ksz], dtype=np.int32).tofile(f); KT.tofile(f)
        with open(os.path.join(out, f"base{idxk}.txt"), "w") as f:
            f.write(f"{2*kk} {len(edges)}\n")
            for u, v, g in edges: f.write(f"{u} {v} {g}\n")
        print(f"K{idxk} |K|={Ksz} index={kk} base={2*kk}+vertices edges={len(edges)} "
              f"table={fn}.bin base={os.path.join(out, f'base{idxk}.txt')}")
        idxk += 1
    print(f"G'={len(Gp)} Q={Q} subgroups written={idxk}")

if __name__ == "__main__":
    main()
