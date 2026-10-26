#!/usr/bin/env python3
"""lns.py: exact large-neighbourhood search (CP-SAT) for the coverage phase of the hub construction on the DM lift
of W(7) (research/squads/cells/d10D5.md).  The flags (p_i, sigma(p_i)) and the hub graph are fixed; sigma on the other
points is the variable.  cover() mirrors dmhub.c cover_cost() exactly.  Each LNS step frees a set S of non-freed
points (their lines may be permuted among them) and asks CP-SAT for the assignment that covers the most
(freed vertex, opposite target) pairs.  Routes where two variable assignments must hold at once are left out, so the
model under-counts coverage; every accepted step is re-evaluated with cover().

usage: lns.py SOL_IN OUT_PREFIX  env: SECS (total), STEP (seconds per CP-SAT call), SIZE (|S|), SEED, WORKERS
writes OUT_PREFIX.sol (dmhub format, same free/hubgraph/mv/nu lines, new sigma) whenever the cost improves.
"""
import sys, os, time, random
import numpy as np
from ortools.sat.python import cp_model

HERE = os.path.dirname(os.path.abspath(__file__))


def load_gq(fn):
    a = np.fromfile(fn, dtype=np.int32)
    q, N, L = int(a[0]), int(a[1]), int(a[2])
    pts = a[3:3 + L * (q + 1)].reshape(L, q + 1).astype(np.int64)
    lof = [[] for _ in range(N)]
    for l in range(L):
        for p in pts[l]: lof[p].append(l)
    return q, N, pts, np.array(lof, dtype=np.int64)


Q, N, PTS, LOF = load_gq(os.path.join(HERE, 'gq', 'gq_q7.bin'))
INC = np.zeros((N, N), bool)
for l in range(N): INC[PTS[l], l] = True
PM = (INC.astype(np.int32) @ INC.T.astype(np.int32)) > 0; np.fill_diagonal(PM, False)   # collinear, a != b
LM = (INC.T.astype(np.int32) @ INC.astype(np.int32)) > 0; np.fill_diagonal(LM, False)   # concurrent, l != m


def read_sol(fn):
    rows = {}
    for ln in open(fn):
        t = ln.split()
        if t: rows[t[0]] = t[1:]
    S = dict(rows=rows)
    S['F'] = [int(x) for x in rows['free']]
    S['sig'] = np.array([int(x) for x in rows['sigma']], dtype=np.int64)
    S['H'] = int(rows['dmhub'][3])
    hg = [int(x) for x in rows.get('hubgraph', [])]
    k = len(S['F']); A = np.zeros((k, k), bool)
    for e in range(0, len(hg), 2): A[hg[e] // S['H'], hg[e + 1] // S['H']] = True
    S['hubadj'] = A
    return S


def write_sol(fn, S, sig, cost):
    rows = dict(S['rows'])
    with open(fn, 'w') as f:
        h = rows['dmhub'][:]
        f.write('dmhub ' + ' '.join(h[:-1] + [str(cost)]) + '\n')
        for key in ('free',):
            f.write(key + ' ' + ' '.join(rows[key]) + '\n')
        f.write('sigma ' + ' '.join(str(int(x)) for x in sig) + '\n')
        for key in ('mv0', 'mv1', 'nu', 'hubgraph'):
            f.write(key + (' ' + ' '.join(rows[key]) if rows.get(key) else '') + '\n')


def cover(F, sig, hubadj, listing=False):
    """exact mirror of dmhub.c cover_cost(): returns number of uncovered (freed vertex, target) pairs"""
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    tot = 0; unc = []
    for i, p in enumerate(F):
        mark = np.zeros(N, bool)
        xs = np.nonzero(PM[p] & ~isfree)[0]
        mark[PTS[sig[xs]].ravel()] = True
        for w in LOF[p]:
            if isfreeL[w]: continue
            z = sinv[w]; us = sinv[LOF[z]]; mark[us[~isfree[us]]] = True
        for j in range(k):
            if hubadj[i, j]: mark[PTS[sig[F[j]]]] = True
        opp = ~PM[p]; opp[p] = False
        bad = np.nonzero(opp & ~mark)[0]; tot += len(bad)
        if listing: unc += [(i, 0, int(u)) for u in bad]
        l = sig[p]
        markl = np.zeros(N, bool)
        Ms = np.nonzero(LM[l] & ~isfreeL)[0]
        markl[LOF[sinv[Ms]].ravel()] = True
        for y in PTS[l]:
            if isfree[y]: continue
            zs = PTS[sig[y]]; zs = zs[~isfree[zs]]; markl[sig[zs]] = True
        for j in range(k):
            if hubadj[j, i]: markl[LOF[F[j]]] = True
        oppl = ~LM[l]; oppl[l] = False
        badl = np.nonzero(oppl & ~markl)[0]; tot += len(badl)
        if listing: unc += [(i, 1, int(m)) for m in badl]
    return (tot, unc) if listing else tot


def lns_step(F, sig, hubadj, S, secs, seed, workers):
    """CP-SAT on the neighbourhood S (non-freed points); returns new sigma (or None) and the model objective"""
    S = sorted(set(int(x) for x in S)); T = [int(sig[x]) for x in S]
    inS = np.zeros(N, bool); inS[S] = True; inT = np.zeros(N, bool); inT[T] = True
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    m = cp_model.CpModel()
    Y = {}
    for x in S:
        for L in T: Y[x, L] = m.NewBoolVar('')
    for x in S: m.AddExactlyOne([Y[x, L] for L in T])
    for L in T: m.AddExactlyOne([Y[x, L] for x in S])
    for x in S: m.AddHint(Y[x, int(sig[x])], 1)
    cvars = []; forced = 0; ands = {}
    def AND(a, b):
        key = (a.Index(), b.Index()) if a.Index() < b.Index() else (b.Index(), a.Index())
        v = ands.get(key)
        if v is None:
            v = m.NewBoolVar(''); m.AddImplication(v, a); m.AddImplication(v, b); ands[key] = v
        return v
    for i, p in enumerate(F):
        # ---------- point side
        const = np.zeros(N, bool); lits = {}
        xs = np.nonzero(PM[p] & ~isfree)[0]
        xf = xs[~inS[xs]]; const[PTS[sig[xf]].ravel()] = True
        xv = xs[inS[xs]]
        for w in LOF[p]:
            if isfreeL[w]: continue
            if not inT[w]:
                z = sinv[w]
                for L2 in LOF[z]:
                    if not inT[L2]:
                        u = sinv[L2]
                        if not isfree[u]: const[u] = True
        for j in range(k):
            if hubadj[i, j]: const[PTS[sig[F[j]]]] = True
        opp = ~PM[p]; opp[p] = False
        need = np.nonzero(opp & ~const)[0]
        if len(need):
            needset = set(int(u) for u in need)
            for u in needset: lits[u] = []
            for x in xv:
                for L in T:
                    for u in PTS[L]:
                        u = int(u)
                        if u in needset: lits[u].append(Y[int(x), L])
            for w in LOF[p]:
                w = int(w)
                if isfreeL[w]: continue
                if not inT[w]:
                    z = int(sinv[w])
                    for L2 in LOF[z]:
                        L2 = int(L2)
                        if inT[L2]:
                            for u in S:
                                if u in needset: lits[u].append(Y[u, L2])
                else:
                    for z in S:
                        for L2 in LOF[z]:
                            L2 = int(L2)
                            if not inT[L2]:
                                u = int(sinv[L2])
                                if u in needset and not isfree[u]: lits[u].append(Y[z, w])
                            else:
                                for u in S:
                                    if u in needset: lits[u].append(AND(Y[z, w], Y[u, L2]))
            for u in needset:
                if lits[u]:
                    c = m.NewBoolVar(''); m.AddBoolOr(lits[u]).OnlyEnforceIf(c); cvars.append(c)
                    m.AddHint(c, 1)
                else: forced += 1
        # ---------- line side
        l = int(sig[p]); const = np.zeros(N, bool); lits = {}
        Ms = np.nonzero(LM[l] & ~isfreeL)[0]
        Mf = Ms[~inT[Ms]]; const[LOF[sinv[Mf]].ravel()] = True
        Mv = [int(M) for M in Ms[inT[Ms]]]
        ys = [int(y) for y in PTS[l] if not isfree[y]]
        for y in ys:
            if not inS[y]:
                for z in PTS[sig[y]]:
                    if not isfree[z] and not inS[z]: const[sig[z]] = True
        for j in range(k):
            if hubadj[j, i]: const[LOF[F[j]]] = True
        oppl = ~LM[l]; oppl[l] = False
        need = np.nonzero(oppl & ~const)[0]
        if len(need):
            needset = set(int(x) for x in need)
            for mm in needset: lits[mm] = []
            for M in Mv:
                for y in S:
                    for mm in LOF[y]:
                        mm = int(mm)
                        if mm in needset: lits[mm].append(Y[y, M])
            for y in ys:
                if not inS[y]:
                    for z in PTS[sig[y]]:
                        z = int(z)
                        if not isfree[z] and inS[z]:
                            for mm in T:
                                if mm in needset: lits[mm].append(Y[z, mm])
                else:
                    for L2 in T:
                        for z in PTS[L2]:
                            z = int(z)
                            if not isfree[z] and not inS[z]:
                                mm = int(sig[z])
                                if mm in needset: lits[mm].append(Y[y, L2])
                            elif not isfree[z]:
                                for mm in T:
                                    if mm in needset: lits[mm].append(AND(Y[y, L2], Y[z, mm]))
            for mm in needset:
                if lits[mm]:
                    c = m.NewBoolVar(''); m.AddBoolOr(lits[mm]).OnlyEnforceIf(c); cvars.append(c)
                    m.AddHint(c, 1)
                else: forced += 1
    pw = float(os.environ.get('PLATEAU', 0))
    if pw > 0:   # plateau drift: small random rewards for leaving the current assignment (never outweigh one target)
        import random as _r
        rr = _r.Random(seed); BIG = 1000
        drift = [Y[x, L] * rr.randint(0, int(pw)) for x in S for L in T if L != int(sig[x]) and rr.random() < 0.05]
        m.Maximize(BIG * sum(cvars) + sum(drift))
    else:
        m.Maximize(sum(cvars))
    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = secs
    sol.parameters.num_workers = workers
    sol.parameters.random_seed = seed
    st = sol.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return None, None
    new = sig.copy()
    for x in S:
        for L in T:
            if sol.Value(Y[x, L]): new[x] = L
    model_unc = len(cvars) - sum(int(sol.Value(c)) for c in cvars) + forced
    return new, (model_unc, len(cvars), forced, len(ands), sol.StatusName(st))


def neighbourhood(F, sig, unc, size, rng):
    """points relevant to the current holes, plus random fill"""
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    isfree = np.zeros(N, bool); isfree[F] = True
    cand = []
    holes = list(unc); rng.shuffle(holes)
    for (i, side, t) in holes[:3]:
        p = F[i]; l = int(sig[p])
        if side == 0:
            A = [int(x) for x in np.nonzero(PM[p] & ~isfree)[0]]
            rng.shuffle(A); cand += A[:rng.randint(6, 20)]
            cand += [int(sinv[L]) for L in LOF[t]]          # preimages of lines through the target
            cand += [t] + [int(sinv[w]) for w in LOF[p]]
        else:
            Ms = [int(M) for M in np.nonzero(LM[l])[0]]
            rng.shuffle(Ms); cand += [int(sinv[M]) for M in Ms[:rng.randint(6, 20)]]
            cand += [int(y) for y in PTS[t]]                 # points on the target line
            cand += [int(sinv[t])] + [int(y) for y in PTS[l]]
    bad = isfree.copy()
    if os.environ.get('EXCL', '1') == '1':   # keep the routes linear (the model is then exact): fix the preimages of
        for p in F:                          # lines through freed points and the points on freed lines
            bad[sinv[LOF[p]]] = True; bad[PTS[sig[p]]] = True
    kz = int(os.environ.get('KZ', 6)); c2 = []
    for x in dict.fromkeys(cand):
        if isfree[x]: continue
        if bad[x]:
            if kz > 0: c2.append(x); kz -= 1
        else: c2.append(x)
    cand = c2
    cs = set(cand)
    rest = [x for x in range(N) if not bad[x] and x not in cs]
    rng.shuffle(rest)
    S = cand[:size] + rest[:max(0, size - len(cand))]
    return S


def main():
    S0 = read_sol(sys.argv[1]); out = sys.argv[2]
    F = S0['F']; sig = S0['sig'].copy(); hubadj = S0['hubadj']
    secs = float(os.environ.get('SECS', 600)); step = float(os.environ.get('STEP', 30))
    size = int(os.environ.get('SIZE', 80)); seed = int(os.environ.get('SEED', 1)); workers = int(os.environ.get('WORKERS', 1))
    rng = random.Random(seed)
    cost, unc = cover(F, sig, hubadj, listing=True)
    best = cost
    print('start cost', cost, 'holes', unc[:10], flush=True)
    t0 = time.time(); it = 0
    while time.time() - t0 < secs and cost > 0:
        it += 1
        sz = size if rng.random() < 0.7 else rng.randint(size // 2, int(size * 1.5))
        S = neighbourhood(F, sig, unc, sz, rng)
        tb = time.time()
        new, info = lns_step(F, sig, hubadj, S, step, rng.randint(1, 10 ** 6), workers)
        if new is None: print('it', it, 'no solution'); continue
        c2, u2 = cover(F, new, hubadj, listing=True)
        acc = c2 <= cost
        print('it %d |S| %d model %s exact %d (cur %d) %s %.1fs' % (it, len(S), info, c2, cost, 'ACC' if acc else 'rej', time.time() - tb), flush=True)
        if acc:
            sig, cost, unc = new, c2, u2
            if cost < best:
                best = cost; write_sol(out + '.sol', S0, sig, cost)
                print('  new best', best, 'holes', unc[:10], flush=True)
    write_sol(out + '.final.sol', S0, sig, cost)
    print('final cost', cost, flush=True)


if __name__ == '__main__':
    main()
