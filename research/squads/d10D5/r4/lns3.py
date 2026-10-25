#!/usr/bin/env python3
"""lns3.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: lns2.py with nu variable too.  Each step frees a set S of
points (sigma permuted among them, as in lns2) AND a set PHI of flags (their nu free); a pair is good if its geodesic
parities are mixed (XOR terms over PHI) or it has a route (sigma terms over S).  Exact on the neighbourhood.
env (new): NPHI (|PHI|, default 60), PHI2 (fraction of PHI from second-order flags, default 0.5).
Based on lns2.py:  Constraints (soft, minimised): coverage holes (lns.py model), FLAGDEL D1 holes (d1.py), and coset-0 bad
pairs: every opposite pair whose geodesics have one nu-parity (unmixed, deleted flag edges removed) needs its route
(points a, b: sigma(a), sigma(b) concurrent; lines s, t: sinv(s), sinv(t) collinear).  The neighbourhood S never
contains preimages of lines through freed points or points on freed lines (so coverage and D1 routes stay linear);
unmixed pairs with both ends variable use AND terms.  env: SECS STEP SIZE SEED"""
import sys, os, time, random
import numpy as np
from ortools.sat.python import cp_model
import lns, d1, coverfd

st, c0, fds, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
S0 = lns.read_sol(st); F = S0['F']; k = len(F); FD = set(int(x) for x in fds.split())
tok = open(c0).read().split(); N = lns.N
sig = np.array([int(x) for x in tok[7:7 + N]]); nu = np.array([int(x) for x in tok[7 + 4 * N:7 + 4 * N + N * 8]]) // 3
PTS, LOF, PM, LM = lns.PTS, lns.LOF, lns.PM, lns.LM
hg = [int(x) for x in S0['rows']['hubgraph']]
A = np.zeros((k, k), bool)
for e in range(0, len(hg), 2):
    a, b = hg[e], hg[e + 1]
    if (a % 3 < 2 or a // 3 in FD) and (b % 3 < 2 or b // 3 in FD): A[a // 3, b // 3] = True
isfree = np.zeros(N, bool); isfree[F] = True
# unmixed pairs (independent of sigma)
fp = {}
for l in range(N):
    for kk in range(8): fp[int(PTS[l][kk]), l] = int(nu[l * 8 + kk])
dele = set((F[i], int(sig[F[i]])) for i in FD)
Pp = np.zeros((N, N), np.int32); Cp = np.zeros((N, N), np.int32); Pl = np.zeros((N, N), np.int32); Cl = np.zeros((N, N), np.int32)
for l in range(N):
    pl = [int(x) for x in PTS[l]]
    for a in pl:
        for c in pl:
            if a != c and (a, l) not in dele and (c, l) not in dele: Cp[a, c] = 1; Pp[a, c] = fp[a, l] ^ fp[c, l]
for y in range(N):
    ls = [int(x) for x in LOF[y]]
    for s_ in ls:
        for t in ls:
            if s_ != t and (y, s_) not in dele and (y, t) not in dele: Cl[s_, t] = 1; Pl[s_, t] = fp[y, s_] ^ fp[y, t]
_NG = {}
def unmixed(P, C, opp):
    Cf = C.astype(np.float64); PC = (P * C).astype(np.float64)
    odd = np.rint(PC @ Cf + Cf @ PC - 2 * (PC @ PC)).astype(np.int64)
    key = id(C)
    if key not in _NG: _NG[key] = np.rint(Cf @ Cf).astype(np.int64)
    return opp & ((odd == 0) | (odd == _NG[key]))
oppP = ~PM; np.fill_diagonal(oppP, False); oppL = ~LM; np.fill_diagonal(oppL, False)
_IA = []; _IC = []; _FA = []; _FC = []; _JS = []; _JT = []; _GS = []; _GT = []
for l in range(N):
    pl = [int(x) for x in PTS[l]]
    for ka, a in enumerate(pl):
        for kc, c in enumerate(pl):
            if Cp[a, c]: _IA.append(a); _IC.append(c); _FA.append(l * 8 + ka); _FC.append(l * 8 + kc)
fidx = {}
for l in range(N):
    for kk in range(8): fidx[int(PTS[l][kk]), l] = l * 8 + kk
for y in range(N):
    ls = [int(x) for x in LOF[y]]
    for s_ in ls:
        for t in ls:
            if Cl[s_, t]: _JS.append(s_); _JT.append(t); _GS.append(fidx[y, s_]); _GT.append(fidx[y, t])
_IA, _IC, _FA, _FC = map(np.array, (_IA, _IC, _FA, _FC)); _JS, _JT, _GS, _GT = map(np.array, (_JS, _JT, _GS, _GT))
def build_unmixed(nu):
    global UP, UL, UPl, ULl
    Pp.fill(0); Pl.fill(0)
    Pp[_IA, _IC] = nu[_FA] ^ nu[_FC]
    Pl[_JS, _JT] = nu[_GS] ^ nu[_GT]
    UP = unmixed(Pp, Cp, oppP); UL = unmixed(Pl, Cl, oppL)
    UPl = [tuple(x) for x in np.argwhere(np.triu(UP))]; ULl = [tuple(x) for x in np.argwhere(np.triu(UL))]
build_unmixed(nu)
print('unmixed pairs: points', len(UPl), 'lines', len(ULl), flush=True)

# ---- lns3: geodesic tables (unordered opposite pairs, 8 geodesics x 4 flags each) ----
FI = np.full((N, N), -1, np.int64)
for l in range(N):
    for kk in range(8): FI[int(PTS[l][kk]), l] = l * 8 + kk
LINE = np.full((N, N), -1, np.int64); PTOF = np.full((N, N), -1, np.int64)
for l in range(N):
    pl = [int(x) for x in PTS[l]]
    for a in pl:
        for c in pl:
            if a != c: LINE[a, c] = l
for y in range(N):
    ls = [int(x) for x in LOF[y]]
    for s_ in ls:
        for t in ls:
            if s_ != t: PTOF[s_, t] = y
_pa, _pb, _pf = [], [], []
for a in range(N):
    for b in np.nonzero(oppP[a])[0]:
        if b <= a: continue
        cs = np.nonzero(PM[a] & PM[b])[0]; L1 = LINE[a, cs]; L2 = LINE[cs, b]
        _pa.append(a); _pb.append(int(b)); _pf.append(np.stack([FI[a, L1], FI[cs, L1], FI[cs, L2], FI[b, L2]], 1))
PA = np.array(_pa); PB = np.array(_pb); PF = np.array(_pf)
_pa, _pb, _pf = [], [], []
for s_ in range(N):
    for t in np.nonzero(oppL[s_])[0]:
        if t <= s_: continue
        Ms = np.nonzero(LM[s_] & LM[t])[0]; y1 = PTOF[s_, Ms]; y2 = PTOF[Ms, t]
        _pa.append(s_); _pb.append(int(t)); _pf.append(np.stack([FI[y1, s_], FI[y1, Ms], FI[y2, Ms], FI[y2, t]], 1))
LA = np.array(_pa); LB = np.array(_pb); LF = np.array(_pf); del _pa, _pb, _pf
assert (PF >= 0).all() and (LF >= 0).all() and PF.shape[1:] == (8, 4) and LF.shape[1:] == (8, 4)
ISDEL = np.zeros(N * 8, bool)
for (p_, l_) in dele: ISDEL[FI[p_, l_]] = True
PV = ~ISDEL[PF].any(-1); LV = ~ISDEL[LF].any(-1)
def unm_vec(nu, Fl, V):
    par = nu[Fl].sum(-1) & 1
    return np.where(V, par, 0).max(1) == np.where(V, par, 1).min(1)
def index(Fl, V):   # flag -> pair ids whose valid geodesics contain it (CSR)
    f = np.where(V[:, :, None], Fl, -1).reshape(len(Fl), -1); ids = np.repeat(np.arange(len(Fl)), f.shape[1]); f = f.ravel()
    k = f >= 0; f, ids = f[k], ids[k]; o = np.argsort(f, kind='stable'); f, ids = f[o], ids[o]
    st = np.searchsorted(f, np.arange(N * 8 + 1)); return st, ids
PIX = index(PF, PV); LIX = index(LF, LV)
def set_unmixed(nu):
    global UPv, ULv, UP, UL, UPl, ULl
    UPv = unm_vec(nu, PF, PV); ULv = unm_vec(nu, LF, LV)
    UP = np.zeros((N, N), bool); UP[PA[UPv], PB[UPv]] = True; UP |= UP.T
    UL = np.zeros((N, N), bool); UL[LA[ULv], LB[ULv]] = True; UL |= UL.T
    UPl = [tuple(x) for x in np.argwhere(np.triu(UP))]; ULl = [tuple(x) for x in np.argwhere(np.triu(UL))]
_UP0, _UL0 = UP.copy(), UL.copy()
set_unmixed(nu)
print('lns3 geodesic tables: unmixed agree with lns2:', bool((UP == _UP0).all() and (UL == _UL0).all()), flush=True)

def total(sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    nf = ~isfree
    rP = LM[sig][:, sig] & nf[:, None] & nf[None, :]; nfl = nf[sinv]; rL = PM[sinv][:, sinv] & nfl[:, None] & nfl[None, :]
    c0b = 0 if os.environ.get('NOC0') else int((UP & ~rP).sum() // 2 + (UL & ~rL).sum() // 2)
    cov = coverfd.cover(F, sig, A, FD)
    dd = sum(cp + cl for i, (p, l, cp, cl, h) in enumerate(d1.d1(F, sig)) if i in FD)
    return c0b + cov + dd, (c0b, cov, dd)

def step(sig, Sset, secs, seed, Phi=(), force=None):
    S = sorted(Sset); T = [int(sig[x]) for x in S]; inS = np.zeros(N, bool); inS[S] = True; inT = np.zeros(N, bool); inT[T] = True
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    m = cp_model.CpModel(); Y = {(x, L): m.NewBoolVar('') for x in S for L in T}
    for x in S: m.AddExactlyOne([Y[x, L] for L in T])
    for L in T: m.AddExactlyOne([Y[x, L] for x in S])
    hv = {}
    for x in S:
        for L in T: v = int(sig[x]) == L; m.AddHint(Y[x, L], v); hv[Y[x, L].Index()] = v
    soft = []
    ands = {}
    def AND(a, b):
        key = (a.Index(), b.Index())
        if key not in ands:
            v = m.NewBoolVar(''); m.AddImplication(v, a); m.AddImplication(v, b); ands[key] = v
            hv[v.Index()] = hv.get(a.Index(), False) and hv.get(b.Index(), False); m.AddHint(v, hv[v.Index()])
        return ands[key]
    def need(lits):
        if lits is True: return
        if not lits: soft.append(None); return
        c = m.NewBoolVar(''); m.AddBoolOr(lits).OnlyEnforceIf(c); soft.append(c)
        m.AddHint(c, any(hv.get(l.Index(), False) for l in lits))
    # coverage: reuse lns.lns_step's model by building it on a sub-model is complex; re-derive (linear only, S excludes
    # second-order points so every route is linear)
    isfreeL = np.zeros(N, bool); isfreeL[sig[F]] = True
    for i, p in enumerate(F):
        const = np.zeros(N, bool)
        okx = PM[p] & ~isfree
        if i in FD: okx[PTS[sig[p]]] = False   # FLAGDEL: no route through the deleted own edge p - l
        xs = np.nonzero(okx)[0]; const[PTS[sig[xs[~inS[xs]]]].ravel()] = True
        for w in LOF[p]:
            if isfreeL[w] or inT[w]: continue
            z = sinv[w]; us = sinv[LOF[z]]; ok = ~isfree[us] & ~inS[us] & ~inT[LOF[z]]; const[us[ok]] = True
        for j in range(k):
            if A[i, j]: const[PTS[sig[F[j]]]] = True
        opp = ~PM[p]; opp[p] = False
        for u in np.nonzero(opp & ~const)[0]:
            u = int(u); lits = [Y[int(x), L] for x in xs[inS[xs]] for L in T if u in PTS[L]]
            for w in LOF[p]:
                w = int(w)
                if isfreeL[w]: continue
                if not inT[w]:
                    if inS[u]:
                        z = int(sinv[w]); lits += [Y[u, L] for L in T if z in PTS[L]]
                else:
                    for z in S:
                        if inS[u]:
                            lits += [AND(Y[z, w], Y[u, int(L2)]) for L2 in LOF[z] if inT[L2] and z in PTS[L2]]
                        elif not isfree[u] and z in PTS[sig[u]]:
                            lits.append(Y[z, w])
            need(lits)
        l = int(sig[p]); const = np.zeros(N, bool)
        okM = LM[l] & ~isfreeL
        if i in FD: okM[LOF[p]] = False
        Ms = np.nonzero(okM)[0]; Mf = Ms[~inT[Ms]]; const[LOF[sinv[Mf]].ravel()] = True; Mv = Ms[inT[Ms]]
        for y in PTS[l]:
            if isfree[y] or inS[y]: continue
            zs = PTS[sig[y]]
            for z in zs:
                if not isfree[z] and not inS[z]: const[sig[z]] = True
        for j in range(k):
            if A[j, i]: const[LOF[F[j]]] = True
        oppl = ~LM[l]; oppl[l] = False
        for mm in np.nonzero(oppl & ~const)[0]:
            mm = int(mm); lits = [Y[int(y), int(M)] for M in Mv for y in S if mm in LOF[y]]
            for y in PTS[l]:
                y = int(y)
                if isfree[y]: continue
                if not inS[y]:
                    for z in PTS[sig[y]]:
                        z = int(z)
                        if not isfree[z] and inS[z] and inT[mm]: lits.append(Y[z, mm])
                else:
                    for L2 in T:
                        for z in PTS[L2]:
                            z = int(z)
                            if isfree[z]: continue
                            if not inS[z]:
                                if int(sig[z]) == mm: lits.append(Y[y, L2])
                            elif inT[mm]: lits.append(AND(Y[y, L2], Y[z, mm]))
            need(lits)
    # D1 (FLAGDEL flags): sources are fixed (preimages of lines through p, lines sigma(y) for y on l)
    for i in FD:
        p = F[i]; l = int(sig[p])
        for L in LOF[p]:
            if L == l or isfreeL[L]: continue
            v = int(sinv[L])
            if v in PTS[l]: continue
            for u in PTS[l]:
                u = int(u)
                if u == p or (isfree[u] and PM[u, v]): continue
                ok = False; lits = []
                for x in np.nonzero(PM[v] & ~isfree)[0]:
                    x = int(x)
                    if not inS[x]:
                        if u in PTS[sig[x]]: ok = True; break
                    else: lits += [Y[x, L2] for L2 in T if u in PTS[L2]]
                if not ok and not isfree[u]:
                    for L2 in LOF[v]:
                        if isfreeL[L2]: continue
                        if not inT[L2]:
                            if int(sinv[L2]) in PTS[sig[u]]: ok = True; break
                        else: lits += [Y[z, int(L2)] for z in S if z in PTS[sig[u]]]
                need(True if ok else lits)
        for y in PTS[l]:
            y = int(y)
            if y == p or isfree[y]: continue
            sl = int(sig[y])
            if sl in LOF[p]: continue
            for t in LOF[p]:
                t = int(t)
                if t == l or (isfreeL[t] and LM[t, sl]): continue
                ok = False; lits = []
                for M in np.nonzero(LM[sl] & ~isfreeL)[0]:
                    M = int(M)
                    if not inT[M]:
                        if int(sinv[M]) in PTS[t]: ok = True; break
                    else: lits += [Y[w, M] for w in S if w in PTS[t]]
                if not ok and not isfreeL[t]:
                    zt = int(sinv[t])
                    for y2 in PTS[sl]:
                        y2 = int(y2)
                        if isfree[y2]: continue
                        if not inS[y2]:
                            if zt in PTS[sig[y2]]: ok = True; break
                        else: lits += [Y[y2, L2] for L2 in T if zt in PTS[L2]]
                need(True if ok else lits)
    # coset-0 (lns3): nu variables on PHI; pair good iff mixed (XOR terms) or routed (sigma terms)
    inPhi = np.zeros(N * 8, bool); inPhi[list(Phi)] = True
    Vn = {}
    nuh = nu
    for f in Phi:
        v = m.NewBoolVar(''); Vn[f] = v; m.AddHint(v, bool(nuh[f])); hv[v.Index()] = bool(nuh[f]); hv[v.Not().Index()] = not nuh[f]
    hard_ok = [force is None]; fbv = [None]
    xors = {}
    def mixterms(Fk, Vk):
        """None if mixed regardless of PHI, else the list of literals (one true <=> mixed)"""
        gs = [g for g in range(8) if Vk[g]]
        W = []; C = []
        for g in gs:
            w = frozenset(int(f) for f in Fk[g] if inPhi[f]); c = 0
            for f in Fk[g]:
                if not inPhi[f]: c ^= int(nu[f])
            W.append(w); C.append(c)
        r = next((i for i in range(len(gs)) if not W[i]), 0)
        lits = []; seen = set()
        for i in range(len(gs)):
            if i == r: continue
            w = W[i] ^ W[r]; d = C[i] ^ C[r]
            if not w:
                if d: return None
                continue
            if (w, d) in seen: continue
            seen.add((w, d))
            if len(w) == 1:
                f = next(iter(w)); lits.append(Vn[f] if d == 0 else Vn[f].Not())
            else:
                if (w, d) not in xors:
                    x = m.NewBoolVar(''); vs = [Vn[f] for f in sorted(w)]
                    m.AddBoolXOr(([x.Not()] if d == 0 else [x]) + vs)
                    val = (sum(int(nuh[f]) for f in w) & 1) ^ d; m.AddHint(x, bool(val)); hv[x.Index()] = bool(val); hv[x.Not().Index()] = not val
                    xors[w, d] = x
                lits.append(xors[w, d])
        return lits
    def touched(IX, Phi):
        st, ids = IX
        if not len(Phi): return np.zeros(0, np.int64)
        return np.unique(np.concatenate([ids[st[f]:st[f + 1]] for f in Phi]))
    for (Ar, Br, Fl, Vl, Uv, IX, pts_side) in ((PA, PB, PF, PV, UPv, PIX, True), (LA, LB, LF, LV, ULv, LIX, False)):
        if os.environ.get('NOC0'): break
        tch = touched(IX, list(Phi))
        cand = np.union1d(np.nonzero(Uv)[0], tch)
        if len(tch):   # drop touched pairs whose PHI-free geodesics are already mixed
            tPhi = np.zeros(len(Ar), bool); tPhi[tch] = True
        else: tPhi = np.zeros(len(Ar), bool)
        Fc = Fl[cand]; Vc = Vl[cand]; ph = inPhi[Fc].any(-1); cpar = (np.where(inPhi[Fc], 0, nu[Fc]).sum(-1) & 1)
        constg = Vc & ~ph
        cmixed = (np.where(constg, cpar, 0).max(1) != np.where(constg, cpar, 1).min(1)) & constg.any(1)
        for kk in np.nonzero(~cmixed)[0]:
            pid = int(cand[kk]); a, b = int(Ar[pid]), int(Br[pid])
            if pts_side:
                fa, fb = isfree[a], isfree[b]; ia, ib = inS[a], inS[b]
            else:
                pa_, pb_ = int(sinv[a]), int(sinv[b]); fa, fb = isfree[pa_], isfree[pb_]; ia, ib = inT[a], inT[b]
            rl = []
            if not (fa or fb):
                if not ia and not ib:
                    if (LM[sig[a], sig[b]] if pts_side else PM[sinv[a], sinv[b]]): continue
                elif pts_side:
                    if ia and ib:   # both endpoints move: approximate (one of them keeps its line); exact check follows
                        sa, sb = int(sig[a]), int(sig[b])
                        rl = [AND(Y[a, L], Y[b, sb]) for L in T if LM[L, sb]] + [AND(Y[b, L], Y[a, sa]) for L in T if LM[L, sa]]
                        if LM[sa, sb]: rl.append(AND(Y[a, sa], Y[b, sb]))
                    else:
                        x, o = (a, b) if ia else (b, a); rl = [Y[x, L] for L in T if LM[L, sig[o]]]
                else:
                    if ia and ib:
                        xa, xb = int(sinv[a]), int(sinv[b])
                        rl = [AND(Y[x, a], Y[xb, b]) for x in S if PM[x, xb]] + [AND(Y[w, b], Y[xa, a]) for w in S if PM[w, xa]]
                        if PM[xa, xb]: rl.append(AND(Y[xa, a], Y[xb, b]))
                    else:
                        L, o = (a, int(sinv[b])) if ia else (b, int(sinv[a])); rl = [Y[x, L] for x in S if PM[x, o]]
            if tPhi[pid]:
                mt = mixterms(Fl[pid], Vl[pid])
                if mt is None: continue
            else:
                if not Uv[pid]: continue
                mt = []
            if force is not None and force == (pts_side, pid):
                if not (mt + rl): return None, None
                need(mt + rl); fbv[0] = soft[-1]; hard_ok[0] = True; continue
            need(mt + rl)
    if not hard_ok[0]: return None, None
    cv = [c for c in soft if c is not None]; forced = len(soft) - len(cv)
    FW = int(os.environ.get('FW', 2))
    m.Maximize(sum(cv) + ((FW - 1) * fbv[0] if fbv[0] is not None else 0))
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = secs; sol.parameters.num_workers = 1; sol.parameters.random_seed = seed
    r = sol.Solve(m)
    if r not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return None, None
    new = sig.copy()
    for x in S:
        for L in T:
            if sol.Value(Y[x, L]): new[x] = L
    nnu = {f: int(sol.Value(v)) for f, v in Vn.items()}
    return (new, nnu), (len(cv) - sum(int(sol.Value(c)) for c in cv) + forced, len(cv), len(ands), sol.StatusName(r))

secs = float(os.environ.get('SECS', 600)); stp = float(os.environ.get('STEP', 20)); size = int(os.environ.get('SIZE', 50))
rng = random.Random(int(os.environ.get('SEED', 1)))
cur, parts = total(sig); print('start', cur, parts, flush=True)
sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
banned = isfree.copy(); second = np.zeros(N, bool)
for i, p in enumerate(F):
    if i in FD: banned[sinv[LOF[p]]] = True; banned[PTS[sig[p]]] = True
    else: second[sinv[LOF[p]]] = True; second[PTS[sig[p]]] = True
second &= ~banned
KZ = int(os.environ.get('KZ', 4))
def neigh(sig, size):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    nf = ~isfree
    rP = LM[sig][:, sig] & nf[:, None] & nf[None, :]; nfl = nf[sinv]; rL = PM[sinv][:, sinv] & nfl[:, None] & nfl[None, :]
    bp = np.argwhere(np.triu(UP & ~rP)); bl = np.argwhere(np.triu(UL & ~rL))
    cand = []
    for a, b in bp: cand += [int(a), int(b)] + [int(sinv[M]) for y in PTS[sig[b]] for M in LOF[y]][:12] + [int(sinv[M]) for y in PTS[sig[a]] for M in LOF[y]][:12]
    for s_, t in bl: cand += [int(sinv[s_]), int(sinv[t])] + [int(w) for w in np.nonzero(PM[sinv[t]])[0]][:12]
    dh = [h for i, (p, l, cp, cl, hs) in enumerate(d1.d1(F, sig)) if i in FD for h in hs]
    rng.shuffle(dh)
    for kind, src, t in dh[:4]:
        if kind == 'pt':   # v = src, u = t: x ~ v gets a line through u
            xs = [int(x) for x in np.nonzero(PM[src])[0]]; rng.shuffle(xs)
            cand += xs[:10] + [int(sinv[L]) for L in LOF[t]]
        else:              # line s = src, line t: a line M ~ s goes to a point on t
            Ms = [int(M) for M in np.nonzero(LM[src])[0]]; rng.shuffle(Ms)
            cand += [int(sinv[M]) for M in Ms[:10]] + [int(w) for w in PTS[t]]
    rng.shuffle(cand)
    Sset = []; kz = KZ
    for x in dict.fromkeys(cand):
        if banned[x]: continue
        if second[x]:
            if kz <= 0: continue
            kz -= 1
        Sset.append(x)
    Sset = Sset[:2 * size // 3]
    rest = [x for x in range(N) if not banned[x] and not second[x] and x not in set(Sset)]; rng.shuffle(rest)
    return Sset + rest[:size - len(Sset)], bp, bl
def write(sig):
    with open(out, 'w') as f:
        f.write(' '.join(tok[:4]) + ' %d\n' % cur + ' '.join(tok[5:7]) + '\n')
        f.write(' '.join(map(str, sig)) + '\n' + ' '.join(map(str, sig)) + '\n')
        f.write(' '.join(tok[7 + 2 * N:7 + 3 * N]) + '\n' + ' '.join(tok[7 + 3 * N:7 + 4 * N]) + '\n')
        f.write(' '.join(str(3 * v) for v in nu) + '\n')
def c0count(sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    nf = ~isfree
    rP = LM[sig][:, sig] & nf[:, None] & nf[None, :]; nfl = nf[sinv]; rL = PM[sinv][:, sinv] & nfl[:, None] & nfl[None, :]
    bP = UP & ~rP; bL = UL & ~rL
    n = int(bP.sum() // 2 + bL.sum() // 2)
    if not os.environ.get('WSCORE'): return n
    mv = ~banned          # movable points (second-order points count as movable)
    mvl = mv[sinv]        # line holders movable
    hardP = bP & ~mv[:, None] & ~mv[None, :]; hardL = bL & ~mvl[:, None] & ~mvl[None, :]
    return n + 10 * int(hardP.sum() // 2 + hardL.sum() // 2)
NPHI = int(os.environ.get('NPHI', 60)); PHI2 = float(os.environ.get('PHI2', 0.5))
def geo_flags(pts_side, pid):
    Fl, Vl = (PF, PV) if pts_side else (LF, LV)
    return [int(f) for g in range(8) if Vl[pid, g] for f in Fl[pid, g]]
def bad_ids(sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N); nf = ~isfree
    rp = nf[PA] & nf[PB] & LM[sig[PA], sig[PB]]; rl = nf[sinv[LA]] & nf[sinv[LB]] & PM[sinv[LA], sinv[LB]]
    return np.nonzero(UPv & ~rp)[0], np.nonzero(ULv & ~rl)[0], rp, rl
def choose_phi(sig):
    bp, bl, rp, rl = bad_ids(sig)
    first = []
    for pid in bp: first += geo_flags(True, int(pid))
    for pid in bl: first += geo_flags(False, int(pid))
    first = [f for f in dict.fromkeys(first) if not ISDEL[f]]; rng.shuffle(first)
    n1 = max(1, int(NPHI * (1 - PHI2))); phi = first[:n1]
    # second order: flags on geodesics of pairs that a first-order flip would unmix (critical, unrouted pairs)
    sec = []
    for f in phi[:12]:
        for (Fl, Vl, IX, rr, side) in ((PF, PV, PIX, rp, True), (LF, LV, LIX, rl, False)):
            st, ids = IX; ps = ids[st[f]:st[f + 1]]; ps = ps[~rr[ps]]
            if not len(ps): continue
            nu[f] ^= 1; um = unm_vec(nu, Fl[ps], Vl[ps]); nu[f] ^= 1
            for pid in ps[um]: sec += geo_flags(side, int(pid))
    sec = [f for f in dict.fromkeys(sec) if not ISDEL[f] and f not in set(phi)]; rng.shuffle(sec)
    phi += sec[:NPHI - len(phi)]
    if len(phi) < NPHI:
        more = [f for f in first[n1:] if f not in set(phi)]; phi += more[:NPHI - len(phi)]
    return phi
def write(sig):
    with open(out, 'w') as f:
        f.write(' '.join(tok[:4]) + ' %d\n' % cur + ' '.join(tok[5:7]) + '\n')
        f.write(' '.join(map(str, sig)) + '\n' + ' '.join(map(str, sig)) + '\n')
        f.write(' '.join(tok[7 + 2 * N:7 + 3 * N]) + '\n' + ' '.join(tok[7 + 3 * N:7 + 4 * N]) + '\n')
        f.write(' '.join(str(3 * v) for v in nu) + '\n')
def crit(f, sig, rp, rl):
    # pairs (side, pid) that flipping f alone would newly unmix and that have no route now
    out = []
    for (Fl, Vl, IX, rr, side, Uv) in ((PF, PV, PIX, rp, True, UPv), (LF, LV, LIX, rl, False, ULv)):
        st, ids = IX; ps = ids[st[f]:st[f + 1]]; ps = ps[~rr[ps] & ~Uv[ps]]
        if not len(ps): continue
        nu[f] ^= 1; um = unm_vec(nu, Fl[ps], Vl[ps]); nu[f] ^= 1
        out += [(side, int(p)) for p in ps[um]]
    return out
def focus(sig):
    # one bad pair B, one of its flags f (forced flip), PHI = f + flags of f's critical pairs, S = their endpoints + route enablers
    bp, bl, rp, rl = bad_ids(sig)
    allb = [(True, int(p)) for p in bp] + [(False, int(p)) for p in bl]
    side, pid = allb[rng.randrange(len(allb))]
    fl = [f for f in dict.fromkeys(geo_flags(side, pid)) if not ISDEL[f]]
    rng.shuffle(fl)
    phi = list(fl); cps = []
    for f in fl[:int(os.environ.get('NF1', 6))]:
        c = crit(f, sig, rp, rl); rng.shuffle(c); cps += c
        for s2, q in c:
            phi += [g for g in geo_flags(s2, q) if not ISDEL[g]]
    phi = list(dict.fromkeys(phi))[:NPHI]; f = (side, pid)
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    S = []
    NE = int(os.environ.get('NENAB', 6))
    for s2, q in cps + [(side, pid)]:
        if s2: a, b = int(PA[q]), int(PB[q])
        else: a, b = int(sinv[LA[q]]), int(sinv[LB[q]])
        if isfree[a] or isfree[b]: continue
        ends = [x for x in (a, b) if not banned[x]]
        if not ends: continue
        x = rng.choice(ends); o = b if x == a else a
        if s2: en = [int(sinv[M]) for M in np.nonzero(LM[sig[o]])[0]]
        else: en = [int(w) for w in np.nonzero(PM[o])[0]]
        rng.shuffle(en); S += [x] + [e for e in en if e not in (a, b)][:NE]
    Sset = []; kz = KZ
    for x in dict.fromkeys(S):
        if banned[x]: continue
        if second[x]:
            if kz <= 0: continue
            kz -= 1
        Sset.append(x)
    Sset = Sset[:size]
    if len(Sset) < size:
        rest = [x for x in range(N) if not banned[x] and not second[x] and x not in set(Sset)]; rng.shuffle(rest)
        Sset += rest[:size - len(Sset)]
    return Sset, phi, f, len(cps)
tabu = []; FOCUS = int(os.environ.get('FOCUS', 0))
best = cur; t0 = time.time(); it = 0
while cur > 0 and time.time() - t0 < secs:
    it += 1
    if FOCUS:
        Sset, phi, ff, ncp = focus(sig)
    else:
        Sset, _, _ = neigh(sig, size); phi = choose_phi(sig); ff = None
    tb = time.time(); res, info = step(sig, Sset, stp, rng.randint(1, 10 ** 6), phi, ff)
    if res is None: print('no solution', flush=True); continue
    new, nnu = res
    nu_old = nu.copy()
    for f, v in nnu.items(): nu[f] = v
    set_unmixed(nu)
    c2, p2 = total(new)
    nfl = int((nu != nu_old).sum())
    print('it %d |S| %d |PHI| %d model %s exact %d %s flips %d (cur %d) %.1fs' % (it, len(Sset), len(phi), info, c2, p2, nfl, cur, time.time() - tb), flush=True)
    if c2 <= cur or (FOCUS and float(os.environ.get('FT', 0)) > 0 and rng.random() < np.exp(-(c2 - cur) / float(os.environ['FT']))):
        sig, cur = new, c2
        if cur < best or cur == 0: best = cur; write(sig)
    else:
        nu[:] = nu_old; set_unmixed(nu)
if cur == best: write(sig)
print('final', cur, total(sig)[1])
