"""relax.py (card c8): CP-SAT relaxation with coverage constraints of a chosen subset of (flag, side) pairs.
The freed structure (all 10 freed points, their lines, hub graph) is kept as in lns.py; only the coverage targets of
the chosen pairs are modelled. sigma is variable on S (non-freed points; their lines are permuted among S)."""
import sys, os, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4'); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from ortools.sat.python import cp_model
import lns
from lns import N, PTS, LOF, PM, LM

def cover_sub(F, sig, hubadj, cons):
    """uncovered targets restricted to cons; mirror of lns.cover (same masks), returns (count, list)"""
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    unc = []
    for i, p in enumerate(F):
        if (i, 0) in cons:
            mark = np.zeros(N, bool)
            xs = np.nonzero(PM[p] & ~isfree)[0]; mark[PTS[sig[xs]].ravel()] = True
            for w in LOF[p]:
                if isfreeL[w]: continue
                z = sinv[w]; us = sinv[LOF[z]]; mark[us[~isfree[us]]] = True
            for j in range(k):
                if hubadj[i, j]: mark[PTS[sig[F[j]]]] = True
            opp = ~PM[p]; opp[p] = False
            unc += [(i, 0, int(u)) for u in np.nonzero(opp & ~mark)[0]]
        if (i, 1) in cons:
            l = sig[p]; markl = np.zeros(N, bool)
            Ms = np.nonzero(LM[l] & ~isfreeL)[0]; markl[LOF[sinv[Ms]].ravel()] = True
            for y in PTS[l]:
                if isfree[y]: continue
                zs = PTS[sig[y]]; zs = zs[~isfree[zs]]; markl[sig[zs]] = True
            for j in range(k):
                if hubadj[j, i]: markl[LOF[F[j]]] = True
            oppl = ~LM[l]; oppl[l] = False
            unc += [(i, 1, int(m)) for m in np.nonzero(oppl & ~markl)[0]]
    return len(unc), unc

def model(F, sig, hubadj, S, cons, secs=120, workers=1, seed=1, hint=True):
    """maximise covered targets among cons, sigma variable on S (lines T = sig[S] permuted among S)."""
    S = sorted(set(int(x) for x in S)); T = [int(sig[x]) for x in S]
    inS = np.zeros(N, bool); inS[S] = True; inT = np.zeros(N, bool); inT[T] = True
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    k = len(F); isfree = np.zeros(N, bool); isfree[F] = True
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    m = cp_model.CpModel(); Y = {}
    for x in S:
        for L in T: Y[x, L] = m.NewBoolVar('')
    for x in S: m.AddExactlyOne([Y[x, L] for L in T])
    for L in T: m.AddExactlyOne([Y[x, L] for x in S])
    if hint:
        for x in S:
            for L in T: m.AddHint(Y[x, L], int(sig[x] == L))
    cvars = []; forced = 0; ands = {}; nand = [0]
    def AND(a, b):
        key = (a.Index(), b.Index()) if a.Index() < b.Index() else (b.Index(), a.Index())
        v = ands.get(key)
        if v is None:
            v = m.NewBoolVar(''); m.AddImplication(v, a); m.AddImplication(v, b); ands[key] = v
        return v
    for (i, side) in cons:
        p = F[i]
        if side == 0:
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
                            if u in needset: lits[u].append((int(x), L))
                for w in LOF[p]:
                    w = int(w)
                    if isfreeL[w]: continue
                    if not inT[w]:
                        z = int(sinv[w])
                        for L2 in LOF[z]:
                            L2 = int(L2)
                            if inT[L2]:
                                for u in S:
                                    if u in needset: lits[u].append((u, L2))
                    else:
                        for z in S:
                            for L2 in LOF[z]:
                                L2 = int(L2)
                                if not inT[L2]:
                                    u = int(sinv[L2])
                                    if u in needset and not isfree[u]: lits[u].append((z, w))
                                else:
                                    for u in S:
                                        if u in needset: raise RuntimeError('AND route')
                for u in needset:
                    if lits[u]:
                        c = m.NewBoolVar(''); m.AddBoolOr([Y[k2] for k2 in lits[u]]).OnlyEnforceIf(c); cvars.append(c)
                        if hint: m.AddHint(c, int(any(sig[x2] == L2 for (x2, L2) in lits[u])))
                    else: forced += 1
        else:
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
                            if mm in needset: lits[mm].append((y, M))
                for y in ys:
                    if not inS[y]:
                        for z in PTS[sig[y]]:
                            z = int(z)
                            if not isfree[z] and inS[z]:
                                for mm in T:
                                    if mm in needset: lits[mm].append((z, mm))
                    else:
                        for L2 in T:
                            for z in PTS[L2]:
                                z = int(z)
                                if not isfree[z] and not inS[z]:
                                    mm = int(sig[z])
                                    if mm in needset: lits[mm].append((y, L2))
                                elif not isfree[z]:
                                    for mm in T:
                                        if mm in needset: raise RuntimeError('AND route')
                for mm in needset:
                    if lits[mm]:
                        c = m.NewBoolVar(''); m.AddBoolOr([Y[k2] for k2 in lits[mm]]).OnlyEnforceIf(c); cvars.append(c)
                        if hint: m.AddHint(c, int(any(sig[x2] == L2 for (x2, L2) in lits[mm])))
                    else: forced += 1
    if os.environ.get('FIX') == '1':
        for x in S: m.Add(Y[x, int(sig[x])] == 1)
    m.Maximize(sum(cvars)) if cvars else None
    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = secs
    sol.parameters.num_workers = workers
    sol.parameters.random_seed = seed
    t0 = time.time(); st = sol.Solve(m); dt = time.time() - t0
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None, dict(status=sol.StatusName(st), secs=round(dt, 1))
    new = sig.copy()
    for x in S:
        for L in T:
            if sol.Value(Y[x, L]): new[x] = L
    unc_model = len(cvars) - sum(int(sol.Value(c)) for c in cvars) + forced
    return new, dict(status=sol.StatusName(st), unc_model=unc_model, targets=len(cvars) + forced, forced=forced,
                     vars=len(Y), ands=len(ands), secs=round(dt, 1), bound=sol.BestObjectiveBound() if cvars else 0)

def linear_S(F, sig):
    """non-freed points whose lines are not freed, not preimages of lines through freed points, not on freed lines:
    every route then uses at most one variable assignment, so the model is exact"""
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    isfree = np.zeros(N, bool); isfree[F] = True
    bad = isfree.copy()
    for p in F:
        bad[sinv[LOF[p]]] = True; bad[PTS[sig[p]]] = True
    return [int(x) for x in np.nonzero(~bad)[0]]
