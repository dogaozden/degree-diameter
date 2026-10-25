#!/usr/bin/env python3
"""tm_build.py: the typed five-level (14,7) graph of research/squads/cells/d16D7.md (levels HDHDH of H(11), identity
matchings on the six friendly transitions with the freed sets R_H, R_L of a typed5s .sol) with the mirrored surgery of
research/cell147/mirror/ added on the four non-friendly transitions:
  4->0, 0->2, 2->4 (H -> H): (p, j) ~ (sigma(p), j+k) for points p not in R' (R' = the 768-point mirrored set);
  1->3 (D -> D):             (l, 1) ~ (sigma^-1(l), 3) for lines l not in sigma(R').
sigma (points -> lines) and R' are those of the (14,7) 1,774,632 graph (a multi_sol .sol): R' non-collinear, sigma(R')
non-concurrent and sigma(Gamma_2(x)) = Gamma_2(sigma(x)) for x in R' (all re-checked here), so each transition satisfies
(H1)-(H3) of the one-transition surgery theorem (d16D7.md). Every deleted matching edge leaves one free slot; line-side
hub h takes the h-th free A-slot of every level, point-side hub h the h-th free B-slot (slot lists in a fixed order).
Hub graph: 9 seeded random perfect matchings between line-side and point-side hubs, or the explicit edge list of a
.sol; same-side distances <= 6 are checked here (bitsets). Vertex numbering as typed5s: (x, level j) = 2Nj + kind*N + x
(kind 0 = point of H, 1 = line); line-side hubs 2N*5 + h, point-side hubs 2N*5 + K + h.
usage: tm_build.py make HEXBIN TYPED_SOL MIRROR_SOL HUBSEED OUT.sol OUT.edges
       tm_build.py build HEXBIN SOL OUT.edges        (SOL names the two input .sol files, in the same directory)"""
import sys, os, hashlib
import numpy as np


def main():
    mode = sys.argv[1]
    if mode == 'make':
        hexfn, solfn, mirfn, offs, solout, outfn = sys.argv[2:8]; hubE = None; hubK = None
    else:
        hexfn, mysol, outfn = sys.argv[2:5]; d = os.path.dirname(os.path.abspath(mysol))
        man = open(mysol).read().split('\n')
        assert man[0].split()[0] == 'typedmirror'
        solfn = os.path.join(d, man[1].split()[1]); mirfn = os.path.join(d, man[2].split()[1])
        for line, fn in ((man[1], solfn), (man[2], mirfn)):
            assert hashlib.sha256(open(fn, 'rb').read()).hexdigest() == line.split()[2], ('sha256 mismatch', fn)
        assert man[3].split()[0] == 'hubs'; hubK = (int(man[3].split()[1]), int(man[3].split()[2]))
        nh = int(man[4].split()[1])
        hubE = np.array([[int(v) for v in t.split()] for t in man[5:5 + nh]], dtype=np.int64)
    b = open(hexfn, 'rb').read()
    q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
    Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
    order = np.lexsort((flat_l, flat_p))
    PL = flat_l[order].reshape(N, Q1)
    tok = open(solfn).read().split(); ti = 0
    def nxt():
        nonlocal ti
        ti += 1
        return tok[ti - 1]
    assert nxt() == 'typed5s'
    qq, NN, L, T, m, n0 = int(nxt()), int(nxt()), int(nxt()), nxt(), int(nxt()), int(nxt())
    assert (qq, NN) == (q, N) and len(T) == L and L % 2 == 1
    RM = (L - 1) // 2; Delta = q + 1 + RM; dh = Delta - L          # matchings per level, max degree, hub-graph degree
    ty = [1 if c == 'D' else 0 for c in T]
    assert nxt() == 'gmat'
    g = np.array([int(nxt()) for _ in range(9)], dtype=np.int64).reshape(3, 3)
    det = int(round(np.linalg.det(g))) % q
    adjg = np.array([[((g[(j + 1) % 3][(i + 1) % 3] * g[(j + 2) % 3][(i + 2) % 3]
                        - g[(j + 1) % 3][(i + 2) % 3] * g[(j + 2) % 3][(i + 1) % 3])) % q for j in range(3)]
                     for i in range(3)], dtype=np.int64)
    gi = (adjg * pow(det, q - 2, q)) % q
    assert np.array_equal((g @ gi) % q, np.eye(3, dtype=np.int64))
    code = X @ (q ** np.arange(7, dtype=np.int64))
    Y = np.zeros_like(X)
    Y[:, 0:3] = (X[:, 0:3] @ g.T) % q; Y[:, 3] = X[:, 3]; Y[:, 4:7] = (X[:, 4:7] @ gi) % q
    lead = np.argmax(Y != 0, axis=1)
    inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
    Y = (Y * inv[Y[np.arange(N), lead]][:, None]) % q
    pp = np.searchsorted(code, Y @ (q ** np.arange(7, dtype=np.int64)))
    a0, b0 = pp[LP[:, 0]], pp[LP[:, 1]]
    hit = (PL[a0][:, :, None] == PL[b0][:, None, :]).reshape(Lc, -1)
    assert np.all(hit.sum(axis=1) == 1)
    perm = [pp, PL[a0, hit.argmax(axis=1) // Q1]]
    inR = []
    for kd, name in ((0, 'RH'), (1, 'RL')):
        assert nxt() == name
        k = int(nxt()); reps = np.array([int(nxt()) for _ in range(k)], dtype=np.int64)
        s = np.zeros(N, bool); cur = reps.copy()
        for _ in range(m):
            s[cur] = True; cur = perm[kd][cur]
        assert np.array_equal(cur, reps)
        inR.append(s)
    RH, RL = inR
    # mirrored sigma and R'
    mt = open(mirfn).read().split('\n')
    assert mt[0].split()[0] == 'multi' and mt[1].split()[0] == 'freed'
    Rp = np.array([int(v) for v in mt[1].split()[1:]], dtype=np.int64)
    sig = np.array([int(v) for line in mt[3:] for v in line.split()], dtype=np.int64)
    assert len(sig) == N and len(np.unique(sig)) == N
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    inRp = np.zeros(N, bool); inRp[Rp] = True
    inSR = np.zeros(N, bool); inSR[sig[Rp]] = True
    # hypotheses
    assert (RH[LP].sum(1) <= 1).all(), 'R_H collinear'
    assert (RL[PL].sum(1) <= 1).all(), 'R_L concurrent'
    assert (inRp[LP].sum(1) <= 1).all(), "R' collinear"
    assert (inSR[PL].sum(1) <= 1).all(), "sigma(R') concurrent"
    for x in Rp:
        G2x = np.setdiff1d(LP[PL[x]].reshape(-1), [x])            # points collinear with x
        l = sig[x]
        G2l = np.setdiff1d(PL[LP[l]].reshape(-1), [l])             # lines meeting sigma(x)
        assert np.array_equal(np.sort(sig[G2x]), G2l), ('local duality fails at', x)
    print(f"hypotheses OK: |R_H| = {RH.sum()}, |R_L| = {RL.sum()}, |R'| = {len(Rp)} (non-collinear, sigma(R') "
          f"non-concurrent, local duality at all {len(Rp)})", flush=True)
    VID = lambda j, kind, x: j * 2 * N + kind * N + x
    out = []
    for j in range(L):
        out.append(np.stack([VID(j, 0, flat_p), VID(j, 1, flat_l)], axis=1))
    Aslots = [[] for _ in range(L)]; Bslots = [[] for _ in range(L)]
    x = np.arange(N)
    for j in range(L):
        for k in range(1, RM + 1):
            j2 = (j + k) % L
            a, bk = ty[j], 1 - ty[j2]
            if a == bk:                                    # friendly: identity
                img = x; free = RH if a == 0 else RL
            elif a == 0:                                   # H -> H: sigma
                img = sig; free = inRp
            else:                                          # D -> D: sigma^-1
                img = sinv; free = inSR
            keep = ~free
            out.append(np.stack([VID(j, a, x[keep]), VID(j2, bk, img[keep])], axis=1))
            Aslots[j].append(VID(j, a, x[free])); Bslots[j2].append(VID(j2, bk, img[free]))
    Aslots = [np.concatenate(s) for s in Aslots]; Bslots = [np.concatenate(s) for s in Bslots]
    KB = min(len(s) for s in Aslots); KA = min(len(s) for s in Bslots)
    print('free A-slots per level', [len(s) for s in Aslots], 'B-slots', [len(s) for s in Bslots], '-> at most', KB, KA)
    if hubK is None: KB = KA = min(KA, KB)                # equal sides (see the hub graph below)
    else:
        assert hubK[0] <= KB and hubK[1] <= KA; KB, KA = hubK
    print('hubs per side', KB, KA, flush=True)
    NV0 = 2 * N * L; n = NV0 + KB + KA
    for j in range(L):
        out.append(np.stack([NV0 + np.arange(KB), Aslots[j][:KB]], axis=1))        # line-side hubs
    for j in range(L):
        out.append(np.stack([NV0 + KB + np.arange(KA), Bslots[j][:KA]], axis=1))   # point-side hubs
    # hub graph, line-side hub a ~ point-side hub b: dh seeded random perfect matchings (repeated pairs kept once); with
    # equal sides and degree dh a random graph has all same-side distances <= 6 with good probability, so seeds are
    # tried in turn from HUBSEED (make), or the explicit edge list of the .sol is used (build)
    def gen(seed):
        P = np.stack([np.random.default_rng([seed, t]).permutation(KB) for t in range(dh)])
        return np.unique(np.stack([np.tile(np.arange(KB), dh), P.reshape(-1)], axis=1), axis=0)
    def nblist(a, b, Ka):                                  # neighbours b of each node a < Ka, padded to dh
        o = np.argsort(a, kind='stable'); bs = b[o]
        stt = np.searchsorted(a[o], np.arange(Ka + 1)); dg = np.diff(stt)
        assert dg.min() >= 1
        return np.stack([bs[stt[:-1] + np.minimum(t, dg - 1)] for t in range(dh)], axis=1)
    def far_pairs(he, listing=False):                      # same-side hub pairs at distance > 6 in the hub graph
        bad = 0; lst = []
        for side in (0, 1):
            u, v, K, Kv = (he[:, 0], he[:, 1], KB, KA) if side == 0 else (he[:, 1], he[:, 0], KA, KB)
            Mu, Mv = nblist(u, v, K), nblist(v, u, Kv)
            W = (K + 63) // 64; idx = np.arange(K)
            Bt = np.zeros((K, W), np.uint64)
            Bt[idx, idx // 64] |= np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
            for _ in range(3):
                U = Bt[Mv[:, 0]].copy()
                for t in range(1, dh): U |= Bt[Mv[:, t]]
                Bn = Bt.copy()
                for t in range(dh): Bn |= U[Mu[:, t]]
                Bt = Bn
            full = np.full(W, ~np.uint64(0), np.uint64)
            if K % 64: full[-1] = np.uint64((1 << (K % 64)) - 1)
            miss = Bt ^ full
            bad += int(sum(bin(int(w)).count('1') for w in miss[miss != 0]))
            if listing:
                for r, c in zip(*np.nonzero(miss)):
                    wv = int(miss[r, c])
                    lst += [(side, int(r), 64 * int(c) + i) for i in range(64) if wv >> i & 1]
        return (bad, lst) if listing else bad
    if hubE is None:
        he = gen(int(offs)); fp, lst = far_pairs(he, True)
        print(f'hub graph seed {offs}: {fp} same-side (ordered) pairs beyond 6', flush=True)
        rng = np.random.default_rng([int(offs), 99]); tries = 0
        while fp > 0:                                      # degree-preserving 2-switches aimed at a far pair
            tries += 1; assert tries < 5000, 'hub graph repair failed'
            side, u, w = lst[rng.integers(len(lst))]
            E = {(int(a), int(b)) for a, b in he}
            col = 0 if side == 0 else 1                    # u, w on this side; edges (u, p) and (x, y), y ~ w
            nb_u = [e for e in E if e[col] == u]; nb_w = [e for e in E if e[col] == w]
            e1 = nb_u[rng.integers(len(nb_u))]; y = nb_w[rng.integers(len(nb_w))][1 - col]
            cand = [e for e in E if e[1 - col] == y and e[col] != w and e[col] != u]
            if not cand: continue
            e2 = cand[rng.integers(len(cand))]; p_ = e1[1 - col]; x = e2[col]
            n1 = (u, y) if col == 0 else (y, u); n2 = (x, p_) if col == 0 else (p_, x)
            if n1 in E or n2 in E: continue
            E2 = (E - {e1, e2}) | {n1, n2}
            he2 = np.array(sorted(E2), dtype=np.int64); fp2, lst2 = far_pairs(he2, True)
            if fp2 < fp:
                he, fp, lst = he2, fp2, lst2
                print(f'  switch {tries}: {fp} far pairs left', flush=True)
    else:
        he = hubE
    assert (he[:, 0] >= 0).all() and (he[:, 0] < KB).all() and (he[:, 1] >= 0).all() and (he[:, 1] < KA).all()
    assert len(np.unique(he, axis=0)) == len(he)
    assert np.bincount(he[:, 0], minlength=KB).max() <= dh and np.bincount(he[:, 1], minlength=KA).max() <= dh
    assert far_pairs(he) == 0, 'hub graph: same-side distance > 6'
    print('hub graph: same-side distances <= 6 on both sides', flush=True)
    if mode == 'make':
        with open(solout, 'w') as f:
            f.write(f'typedmirror {q} {N} {T} {n}\n')
            for fn in (solfn, mirfn):
                f.write(f'{"typed" if fn == solfn else "mirror"} {os.path.basename(fn)} '
                        f'{hashlib.sha256(open(fn, "rb").read()).hexdigest()}\n')
            f.write(f'hubs {KB} {KA}\nhubgraph {len(he)}\n' + '\n'.join(f'{a} {b}' for a, b in he.tolist()) + '\n')
        print('wrote', solout)
    out.append(np.stack([NV0 + he[:, 0], NV0 + KB + he[:, 1]], axis=1))
    E = np.concatenate(out)
    deg = np.bincount(E.reshape(-1), minlength=n)
    print(f'n = {n}, edges = {len(E)}, degree min {deg.min()} max {deg.max()}, hub graph edges {len(he)}', flush=True)
    assert deg.max() <= Delta
    with open(outfn, 'w') as f:
        f.write('%d\n' % n)
        CH = 1 << 21
        for i in range(0, len(E), CH):
            f.write('\n'.join('%d %d' % (u, v) for u, v in E[i:i + CH].tolist())); f.write('\n')
    print('wrote', outfn)


if __name__ == '__main__':
    main()
