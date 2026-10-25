#!/usr/bin/env python3
"""tm2_build.py: seven-level typed H(11) graph for (15,7) (levels HHDHHDD, research/squads/cells/d16D7.md) with the
mirrored surgery on the nine non-friendly transitions (research/cell147/typedmirror/README.md), generalised:
  - the friendly freed sets R_H (non-collinear points) and R_L (non-concurrent lines) are explicit id lists (no symmetry
    needed), and the line-side and point-side hub counts may differ;
  - the hub graph is an explicit edge list (line-side hub a, point-side hub b), degree <= 15 - 7 = 8.
Construction (as tm_build.py): every level has the incidence edges of H; transition j -> j+k (k = 1, 2, 3) has the
identity on friendly transitions (types differ) minus R_H (H level) or R_L (D level), sigma on H -> H minus R', sigma^-1
on D -> D minus sigma(R').  Every deleted edge leaves a free A-slot at the source and a free B-slot at the target;
line-side hub h takes the h-th free A-slot of every level, point-side hub h the h-th free B-slot (slot lists in the
fixed order: transitions k = 1, 2, 3, then ids increasing).  Vertex ids: (x, level j) = 2Nj + kind*N + x (kind 0 = point,
1 = line); line-side hubs 14N + h, point-side hubs 14N + KB + h.
Hypotheses re-checked here: R_H non-collinear, R_L non-concurrent, R' non-collinear, sigma(R') non-concurrent, local
duality sigma(Gamma_2(x)) = Gamma_2(sigma(x)) at every x in R'.  Same-side hub distances (<= 6) are NOT checked here:
run hubfar.c on the edge list (BFS from all hubs in the full graph).
usage: tm2_build.py slots HEXBIN RH.txt RL.txt MIRROR_SOL                  (prints free slot counts per level)
       tm2_build.py build HEXBIN SOL OUT.edges                            (SOL: typedmirror2 file, see make)
       tm2_build.py make HEXBIN RH.txt RL.txt MIRROR_SOL KB KA HUBEDGES OUT.sol [OUT.edges]"""
import sys, os, hashlib
import numpy as np

T = 'HHDHHDD'; L = 7; RM = 3; Delta = 15


def load_hex(hexfn):
    b = open(hexfn, 'rb').read()
    q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
    order = np.lexsort((flat_l, flat_p)); PL = flat_l[order].reshape(N, Q1)
    return q, N, LP, PL, flat_p, flat_l


def load_mirror(mirfn, N):
    mt = open(mirfn).read().split('\n')
    assert mt[0].split()[0] == 'multi' and mt[1].split()[0] == 'freed'
    Rp = np.array([int(v) for v in mt[1].split()[1:]], dtype=np.int64)
    sig = np.array([int(v) for line in mt[3:] for v in line.split()], dtype=np.int64)
    assert len(sig) == N and len(np.unique(sig)) == N
    return Rp, sig


def check_hyp(N, LP, PL, RH, RL, Rp, sig):
    inRp = np.zeros(N, bool); inRp[Rp] = True
    inSR = np.zeros(N, bool); inSR[sig[Rp]] = True
    assert (RH[LP].sum(1) <= 1).all(), 'R_H collinear'
    assert (RL[PL].sum(1) <= 1).all(), 'R_L concurrent'
    assert (inRp[LP].sum(1) <= 1).all(), "R' collinear"
    assert (inSR[PL].sum(1) <= 1).all(), "sigma(R') concurrent"
    for x in Rp:
        G2x = np.setdiff1d(LP[PL[x]].reshape(-1), [x])
        l = sig[x]
        G2l = np.setdiff1d(PL[LP[l]].reshape(-1), [l])
        assert np.array_equal(np.sort(sig[G2x]), G2l), ('local duality fails at', x)
    print(f"hypotheses OK: |R_H| = {RH.sum()}, |R_L| = {RL.sum()}, |R'| = {len(Rp)} (non-collinear, sigma(R') "
          f"non-concurrent, local duality at all {len(Rp)})", flush=True)
    return inRp, inSR


def base(N, flat_p, flat_l, RH, RL, inRp, inSR, sig):
    ty = [1 if c == 'D' else 0 for c in T]
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    VID = lambda j, kind, x: j * 2 * N + kind * N + x
    out = [np.stack([VID(j, 0, flat_p), VID(j, 1, flat_l)], axis=1) for j in range(L)]
    Aslots = [[] for _ in range(L)]; Bslots = [[] for _ in range(L)]
    x = np.arange(N)
    for j in range(L):
        for k in range(1, RM + 1):
            j2 = (j + k) % L
            a, bk = ty[j], 1 - ty[j2]
            if a == bk:
                img = x; free = RH if a == 0 else RL
            elif a == 0:
                img = sig; free = inRp
            else:
                img = sinv; free = inSR
            keep = ~free
            out.append(np.stack([VID(j, a, x[keep]), VID(j2, bk, img[keep])], axis=1))
            Aslots[j].append(VID(j, a, x[free])); Bslots[j2].append(VID(j2, bk, img[free]))
    Aslots = [np.concatenate(s) for s in Aslots]; Bslots = [np.concatenate(s) for s in Bslots]
    return out, Aslots, Bslots


def readset(fn, N):
    s = np.zeros(N, bool); ids = np.loadtxt(fn, dtype=np.int64).reshape(-1); s[ids] = True
    assert s.sum() == len(ids)
    return s


def write_edges(outfn, n, E):
    with open(outfn, 'w') as f:
        f.write('%d\n' % n)
        CH = 1 << 21
        for i in range(0, len(E), CH):
            f.write('\n'.join('%d %d' % (u, v) for u, v in E[i:i + CH].tolist())); f.write('\n')
    print('wrote', outfn, flush=True)


def assemble(N, out, Aslots, Bslots, KB, KA, he):
    NV0 = 2 * N * L; n = NV0 + KB + KA
    assert KB <= min(len(s) for s in Aslots) and KA <= min(len(s) for s in Bslots)
    out = list(out)
    for j in range(L):
        out.append(np.stack([NV0 + np.arange(KB), Aslots[j][:KB]], axis=1))
    for j in range(L):
        out.append(np.stack([NV0 + KB + np.arange(KA), Bslots[j][:KA]], axis=1))
    assert (he[:, 0] >= 0).all() and (he[:, 0] < KB).all() and (he[:, 1] >= 0).all() and (he[:, 1] < KA).all()
    assert len(np.unique(he, axis=0)) == len(he)
    out.append(np.stack([NV0 + he[:, 0], NV0 + KB + he[:, 1]], axis=1))
    E = np.concatenate(out)
    deg = np.bincount(E.reshape(-1), minlength=n)
    print(f'n = {n}, edges = {len(E)}, degree min {deg.min()} max {deg.max()}, hub graph edges {len(he)}', flush=True)
    assert deg.max() <= Delta
    return n, E


def main():
    mode = sys.argv[1]
    if mode == 'slots':
        hexfn, rhf, rlf, mirfn = sys.argv[2:6]
        q, N, LP, PL, fp, fl = load_hex(hexfn)
        RH, RL = readset(rhf, N), readset(rlf, N); Rp, sig = load_mirror(mirfn, N)
        inRp, inSR = check_hyp(N, LP, PL, RH, RL, Rp, sig)
        out, A, B = base(N, fp, fl, RH, RL, inRp, inSR, sig)
        print('free A-slots per level', [len(s) for s in A], 'B-slots', [len(s) for s in B])
        print('max hubs: line-side', min(len(s) for s in A), 'point-side', min(len(s) for s in B))
        return
    if mode == 'make':
        hexfn, rhf, rlf, mirfn, KB, KA, hef, solout = sys.argv[2:10]; KB, KA = int(KB), int(KA)
        outfn = sys.argv[10] if len(sys.argv) > 10 else None
        q, N, LP, PL, fp, fl = load_hex(hexfn)
        rh = np.loadtxt(rhf, dtype=np.int64).reshape(-1); rl = np.loadtxt(rlf, dtype=np.int64).reshape(-1)
        he = np.loadtxt(hef, dtype=np.int64).reshape(-1, 2)
        with open(solout, 'w') as f:
            f.write(f'typedmirror2 {q} {N} {T} {14 * N + KB + KA}\n')
            f.write(f'mirror {os.path.basename(mirfn)} {hashlib.sha256(open(mirfn, "rb").read()).hexdigest()}\n')
            f.write(f'RH {len(rh)}\n' + '\n'.join(map(str, sorted(rh.tolist()))) + '\n')
            f.write(f'RL {len(rl)}\n' + '\n'.join(map(str, sorted(rl.tolist()))) + '\n')
            f.write(f'hubs {KB} {KA}\nhubgraph {len(he)}\n' + '\n'.join(f'{a} {b}' for a, b in he.tolist()) + '\n')
        print('wrote', solout)
        if outfn is None: return
        mysol = solout
    else:
        hexfn, mysol, outfn = sys.argv[2:5]
        q, N, LP, PL, fp, fl = load_hex(hexfn)
    d = os.path.dirname(os.path.abspath(mysol))
    tok = open(mysol).read().split('\n'); i = 0
    h = tok[i].split(); i += 1
    assert h[0] == 'typedmirror2' and int(h[2]) == N and h[3] == T
    m = tok[i].split(); i += 1
    mirfn = os.path.join(d, m[1])
    assert hashlib.sha256(open(mirfn, 'rb').read()).hexdigest() == m[2], 'mirror sol sha256 mismatch'
    sets = []
    for name in ('RH', 'RL'):
        t = tok[i].split(); i += 1; assert t[0] == name; k = int(t[1])
        ids = np.array([int(v) for v in tok[i:i + k]], dtype=np.int64); i += k
        s = np.zeros(N, bool); s[ids] = True; assert s.sum() == k; sets.append(s)
    RH, RL = sets
    t = tok[i].split(); i += 1; assert t[0] == 'hubs'; KB, KA = int(t[1]), int(t[2])
    t = tok[i].split(); i += 1; assert t[0] == 'hubgraph'; ne = int(t[1])
    he = np.array([[int(v) for v in s.split()] for s in tok[i:i + ne]], dtype=np.int64).reshape(-1, 2)
    Rp, sig = load_mirror(mirfn, N)
    inRp, inSR = check_hyp(N, LP, PL, RH, RL, Rp, sig)
    out, A, B = base(N, fp, fl, RH, RL, inRp, inSR, sig)
    print('free A-slots per level', [len(s) for s in A], 'B-slots', [len(s) for s in B], '-> hubs', KB, KA, flush=True)
    n, E = assemble(N, out, A, B, KB, KA, he)
    assert n == int(h[4])
    write_edges(outfn, n, E)


if __name__ == '__main__':
    main()
