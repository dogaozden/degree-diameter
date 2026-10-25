#!/usr/bin/env python3
"""c2 flag-set local search: minimise mismatch(F) over K pairwise opposite flags of H(8).

  python3 flagls.py run K SEED SECONDS OUT.json [T0 T1 C [INIT.json]]
      K        number of flags (16 for the score)
      SECONDS  wall-clock budget of the annealing run
      OUT.json best flag list so far, written on every improvement, format [[p, l], ...]
      T0, T1   start / end temperature (geometric in time), default 30 and 0.5
      C        candidates sampled per move (the best of them is offered to the Metropolis rule), default 4
      INIT     optional flag list to start from (must have K entries)
  python3 flagls.py verify FLAGS.json      independent check with research/squads/d10D7-r3/tools/hexkit.py

Energy = mismatch = sum_v |#(points not freed, vector v) - #(lines not freed, vector v)|, exactly hexkit.Hex.mismatch.
Membership: bit k of point u is set iff d(p_k,u)=4 and d(l_k,u)=5; bit k of line L iff d(l_k,L)=4 and d(p_k,L)=5.
Move: pick a flag k at random, sample M random flags, keep those opposite to the other K-1 flags (vectorised lookups
in the stored distance arrays), evaluate C of them (2 uint8 BFS each), accept the best by the Metropolis rule.
Distances: uint8 BFS on the incidence graph with boolean frontiers (no cache; memory stays a few MB).
"""
import os, sys, json, struct, time, math
import numpy as np

HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
TOOLS = '/home/user/degree-diameter/research/squads/d10D7-r3/tools'


class Hex:
    def __init__(self, fn=HEX):
        with open(fn, 'rb') as f:
            q, N, L = struct.unpack('3i', f.read(12))
            LP = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
        assert L == N
        flat = LP.ravel()
        order = np.argsort(flat, kind='stable')          # sorted by point; each point has q+1 lines
        lines = np.repeat(np.arange(L, dtype=np.int64), q + 1)
        PL = lines[order].reshape(N, q + 1)
        assert (np.bincount(flat, minlength=N) == q + 1).all()
        self.q, self.N, self.LP, self.PL = q, N, LP, PL

    def bfs(self, x, isline=False):
        """uint8 distances: [0:N] to points, [N:2N] to lines; 255 = unreachable (never happens, connected)."""
        N = self.N
        dist = np.full(2 * N, 255, np.uint8)
        seenP = np.zeros(N, bool); seenL = np.zeros(N, bool)
        if isline:
            seenL[x] = True; dist[N + x] = 0; fr = np.array([x]); onpts = False
        else:
            seenP[x] = True; dist[x] = 0; fr = np.array([x]); onpts = True
        k = 0
        while fr.size:
            k += 1
            m = np.zeros(N, bool)
            if onpts:
                m[self.PL[fr].ravel()] = True; m &= ~seenL
                fr = np.nonzero(m)[0]; seenL[fr] = True; dist[N + fr] = k
            else:
                m[self.LP[fr].ravel()] = True; m &= ~seenP
                fr = np.nonzero(m)[0]; seenP[fr] = True; dist[fr] = k
            onpts = not onpts
        return dist

    def make(self, p, l):
        dp = self.bfs(p, False); dl = self.bfs(l, True); N = self.N
        Sp = (dp[:N] == 4) & (dl[:N] == 5)          # points u: d(p,u)=4, d(l,u)=5
        Sl = (dl[N:] == 4) & (dp[N:] == 5)          # lines L: d(l,L)=4, d(p,L)=5
        return {'p': int(p), 'l': int(l), 'dp': dp, 'dl': dl, 'Sp': Sp, 'Sl': Sl}

    def feasible(self, cP, cL, others):
        """bool mask: candidate flags (cP[i], cL[i]) opposite to every (dp, dl) in others."""
        N = self.N
        ok = np.ones(len(cP), bool); cLN = cL + N
        for dp, dl in others:
            ok &= (dp[cP] == 6) & (dl[cLN] == 6) & (dp[cLN] == 5) & (dl[cP] == 5)
        return ok


def mismatch_from(vp, vl, notP, notL, K):
    if K <= 20:
        cp = np.bincount(vp[notP], minlength=1 << K)
        cl = np.bincount(vl[notL], minlength=1 << K)
        return int(np.abs(cp - cl).sum())
    ux, cx = np.unique(vp[notP], return_counts=True)
    uy, cy = np.unique(vl[notL], return_counts=True)
    allv = np.union1d(ux, uy)
    a = np.zeros(len(allv), np.int64); a[np.searchsorted(allv, ux)] = cx
    b = np.zeros(len(allv), np.int64); b[np.searchsorted(allv, uy)] = cy
    return int(np.abs(a - b).sum())


def state_of(H, flags):
    N = H.N
    vp = np.zeros(N, np.uint32); vl = np.zeros(N, np.uint32)
    notP = np.ones(N, bool); notL = np.ones(N, bool)
    for k, f in enumerate(flags):
        vp |= f['Sp'].astype(np.uint32) << np.uint32(k)
        vl |= f['Sl'].astype(np.uint32) << np.uint32(k)
        notP[f['p']] = False; notL[f['l']] = False
    return vp, vl, notP, notL


def save(fn, flags_pl):
    tmp = fn + '.tmp'
    with open(tmp, 'w') as f:
        json.dump([[int(p), int(l)] for p, l in flags_pl], f)
    os.replace(tmp, fn)


def run(K, seed, secs, out, T0=30.0, T1=0.5, C=4, init=None, M=4000):
    H = Hex(); N, q, PL = H.N, H.q, H.PL
    rng = np.random.default_rng(seed)
    flags = []
    if init:
        for p, l in json.load(open(init)):
            flags.append(H.make(p, l))
        assert len(flags) == K
    while len(flags) < K:                         # random opposite start, greedy
        cP = rng.integers(N, size=M); cL = PL[cP, rng.integers(q + 1, size=M)]
        ok = H.feasible(cP, cL, [(f['dp'], f['dl']) for f in flags])
        idx = np.nonzero(ok)[0]
        if idx.size:
            i = idx[rng.integers(idx.size)]
            flags.append(H.make(cP[i], cL[i]))
    vp, vl, notP, notL = state_of(H, flags)
    E = mismatch_from(vp, vl, notP, notL, K)
    bestE = E; best = [(f['p'], f['l']) for f in flags]
    save(out, best)
    print('start E', E, flush=True)
    t0 = time.time(); last = t0; moves = acc = 0; dEs = []
    while True:
        el = time.time() - t0
        if el >= secs:
            break
        T = T0 * (T1 / T0) ** (el / secs)
        k = int(rng.integers(K)); fk = flags[k]
        others = [(f['dp'], f['dl']) for j, f in enumerate(flags) if j != k]
        cP = rng.integers(N, size=M); cL = PL[cP, rng.integers(q + 1, size=M)]
        idx = np.nonzero(H.feasible(cP, cL, others))[0]
        if idx.size == 0:
            continue
        if idx.size > C:
            idx = rng.choice(idx, C, replace=False)
        bit = np.uint32(1 << k); bestc = None
        for i in idx:
            nf = H.make(cP[i], cL[i])
            vp2 = np.where(nf['Sp'], vp | bit, vp & ~bit)
            vl2 = np.where(nf['Sl'], vl | bit, vl & ~bit)
            nP = notP.copy(); nP[fk['p']] = True; nP[nf['p']] = False
            nL = notL.copy(); nL[fk['l']] = True; nL[nf['l']] = False
            E2 = mismatch_from(vp2, vl2, nP, nL, K)
            if bestc is None or E2 < bestc[0]:
                bestc = (E2, nf, vp2, vl2, nP, nL)
        E2, nf, vp2, vl2, nP, nL = bestc
        dE = E2 - E; dEs.append(dE); moves += 1
        if dE <= 0 or rng.random() < math.exp(-dE / T):
            acc += 1
            flags[k] = nf; vp, vl, notP, notL = vp2, vl2, nP, nL; E = E2
            if E < bestE:
                bestE = E; best = [(f['p'], f['l']) for f in flags]
                save(out, best)
        if time.time() - last > 15:
            last = time.time()
            print('t %.0f T %.2f moves %d acc %.3f E %d best %d med|dE| %.0f' % (
                time.time() - t0, T, moves, acc / max(moves, 1), E, bestE,
                np.median(np.abs(dEs[-500:])) if dEs else -1), flush=True)
    save(out, best)
    print('done moves', moves, 'acc', round(acc / max(moves, 1), 3), 'bestE', bestE, flush=True)
    return bestE


def grow(K, seed, C, out, M=4000):
    """greedy growth: add flags one at a time, each the best of C random feasible candidates (energy at that size)."""
    H = Hex(); N, q, PL = H.N, H.q, H.PL
    rng = np.random.default_rng(seed)
    flags = []; vp = np.zeros(N, np.uint32); vl = np.zeros(N, np.uint32)
    notP = np.ones(N, bool); notL = np.ones(N, bool); t0 = time.time()
    for s in range(K):
        bit = np.uint32(1 << s); bestc = None; got = 0
        while got < C:
            cP = rng.integers(N, size=M); cL = PL[cP, rng.integers(q + 1, size=M)]
            idx = np.nonzero(H.feasible(cP, cL, [(f['dp'], f['dl']) for f in flags]))[0]
            for i in idx[:C - got]:
                nf = H.make(cP[i], cL[i]); got += 1
                vp2 = vp | (nf['Sp'].astype(np.uint32) << np.uint32(s))
                vl2 = vl | (nf['Sl'].astype(np.uint32) << np.uint32(s))
                nP = notP.copy(); nP[nf['p']] = False; nL = notL.copy(); nL[nf['l']] = False
                E2 = mismatch_from(vp2, vl2, nP, nL, s + 1)
                if bestc is None or E2 < bestc[0]:
                    bestc = (E2, nf, vp2, vl2, nP, nL)
        E2, nf, vp, vl, notP, notL = bestc
        flags.append(nf)
        print('grow stage', s + 1, 'E', E2, 'time %.0f' % (time.time() - t0), flush=True)
    save(out, [(f['p'], f['l']) for f in flags])
    return E2


def verify(fn):
    sys.path.insert(0, TOOLS)
    import hexkit
    H = hexkit.Hex(8)
    F = [(int(p), int(l)) for p, l in json.load(open(fn))]
    on = all(l in H.PL[p] for p, l in F)
    pair = all(H.opposite(F[i], F[j]) for i in range(len(F)) for j in range(i))
    print('K', len(F), 'distinct points', len({p for p, l in F}) == len(F), 'flags on lines', on,
          'pairwise_opposite', pair, 'mismatch_hexkit', H.mismatch(F), flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'verify':
        verify(sys.argv[2])
    elif sys.argv[1] == 'grow':
        grow(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    else:
        a = sys.argv[2:]
        K, seed, secs = int(a[0]), int(a[1]), float(a[2]); out = a[3]
        T0 = float(a[4]) if len(a) > 4 else 30.0
        T1 = float(a[5]) if len(a) > 5 else 0.5
        C = int(a[6]) if len(a) > 6 else 4
        init = a[7] if len(a) > 7 else None
        run(K, seed, secs, out, T0, T1, C, init)
