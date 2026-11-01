#!/usr/bin/env python3
"""w14: build the two-subgroup bi-coset table for kbi.c.
A_i = H.x_i (cosets of H), B_j = K.y_j (cosets of K), |H| = |K| = h; S = union of double cosets K.g.H;
A_i ~ B_j iff y_j . x_i^-1 lies in S. Usage: python3 kgrp.py GROUP h HCLASS KCLASS [CONJSEED] -> runs/K_<tag>.bin
HCLASS/KCLASS are indices into the subgroup classes of order h (from grp14.subgroup_classes, seeded), CONJSEED
(optional, >0) conjugates K by a random group element first."""
import sys, os, random, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import grp14

def cosets(G, H):
    Hp = G.P[np.array(H)]
    lab = None
    for k in range(len(H)):
        c = G.idx(Hp[k][G.P])
        lab = c if lab is None else np.minimum(lab, c)
    uniq = np.unique(lab)
    return uniq, np.searchsorted(uniq, lab)     # reps (element indices), coset id of each element

def conj_subgroup(G, K, g):
    """ g^-1 K g  (as element indices) """
    gi = G.Pinv[g]
    out = []
    for k in K:
        x = G.P[g][G.P[k]]       # placeholder to keep shapes clear
        out.append(None)
    Kp = G.P[np.array(K)]
    # (g^-1 k g)[t] = gi[ k[ g[t] ] ]
    Y = gi[Kp[:, G.P[g]]]
    return sorted(G.idx(Y).tolist())

def build(G, H, K, path):
    h = len(H)
    assert len(K) == h
    Hp = G.P[np.array(H)]; Kp = G.P[np.array(K)]
    repH, cidH = cosets(G, H)
    repK, cidK = cosets(G, K)
    M = len(repH); assert len(repK) == M and M * h == G.N
    dc = np.full(G.N, -1, dtype=np.int64)
    deltas = []
    nD = 0
    for g in range(G.N):
        if dc[g] >= 0:
            continue
        A1 = Kp[:, G.P[g]]                              # k o g : h x d
        A1b = np.broadcast_to(A1[:, None, :], (h, h, G.d))
        Hb = np.broadcast_to(Hp[None, :, :], (h, h, G.d))
        prods = np.take_along_axis(A1b, Hb, axis=2).reshape(-1, G.d)   # k o g o h
        ids = np.unique(G.idx(prods))
        dc[ids] = nD
        deltas.append(len(ids) // h)
        nD += 1
    deltas = np.array(deltas, dtype=np.int64)
    T = np.empty((M, M), dtype=np.uint16)
    Kyel = G.P[repK]                                    # M x d (reps y_j)
    for i in range(M):
        xinv = G.Pinv[repH[i]]
        prod = Kyel[:, xinv]                            # (y o x^-1)[t] = y[x^-1[t]]
        T[i] = dc[G.idx(prod)].astype(np.uint16)
    with open(path, "wb") as f:
        f.write(np.array([M, nD], dtype="<i4").tobytes())
        f.write(T.astype("<u2").tobytes())
        f.write(np.minimum(deltas, 255).astype(np.uint8).tobytes())
    return M, nD, np.bincount(deltas, minlength=5)[:5].tolist()

def main():
    name = sys.argv[1]; h = int(sys.argv[2]); hc = int(sys.argv[3]); kc = int(sys.argv[4])
    conjseed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    G = grp14.Grp(grp14.group_gens(name))
    classes = G.subgroup_classes(h, int(os.environ.get("TRIALS", "800")))
    H = classes[hc]
    K = classes[kc]
    tag = f"{name}_h{h}_H{hc}_K{kc}_c{conjseed}"
    if conjseed:
        rnd = random.Random(conjseed)
        g = rnd.randrange(G.N)
        K = conj_subgroup(G, K, g)
    os.makedirs(os.path.join(HERE, "runs"), exist_ok=True)
    binp = os.path.join(HERE, "runs", "K_" + tag + ".bin")
    t = time.time()
    M, nD, cnt = build(G, H, K, binp)
    print(f"[{tag}] M={M} n={2*M} nD={nD} double cosets by delta 1..4: {cnt[1:]}  classes={len(classes)} ({time.time()-t:.1f}s)", flush=True)

if __name__ == "__main__":
    main()
