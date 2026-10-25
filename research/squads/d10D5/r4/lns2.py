#!/usr/bin/env python3
"""lns2.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: exact CP-SAT neighbourhood search for the FLAGDEL endgame with
nu fixed.  Constraints (soft, minimised): coverage holes (lns.py model), FLAGDEL D1 holes (d1.py), and coset-0 bad
pairs: every opposite pair whose geodesics have one nu-parity (unmixed, deleted flag edges removed) needs its route
(points a, b: sigma(a), sigma(b) concurrent; lines s, t: sinv(s), sinv(t) collinear).  The neighbourhood S never
contains preimages of lines through freed points or points on freed lines (so coverage and D1 routes stay linear);
unmixed pairs with both ends variable use AND terms.  env: SECS STEP SIZE SEED"""
import sys, os, time, random
import numpy as np
from ortools.sat.python import cp_model
import lns, d1

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
def unmixed(P, C, opp):
    PC = P * C; odd = PC @ C + C @ PC - 2 * (PC @ PC); ng = C @ C
    return opp & ((odd == 0) | (odd == ng))
oppP = ~PM; np.fill_diagonal(oppP, False); oppL = ~LM; np.fill_diagonal(oppL, False)
def build_unmixed(nu):
    global UP, UL, UPl, ULl
    fp = {}
    for l in range(N):
        for kk in range(8): fp[int(PTS[l][kk]), l] = int(nu[l * 8 + kk])
    Pp.fill(0); Pl.fill(0)
    for l in range(N):
        pl = [int(x) for x in PTS[l]]
        for a in pl:
            for c in pl:
                if Cp[a, c]: Pp[a, c] = fp[a, l] ^ fp[c, l]
    for y in range(N):
        ls = [int(x) for x in LOF[y]]
        for s_ in ls:
            for t in ls:
                if Cl[s_, t]: Pl[s_, t] = fp[y, s_] ^ fp[y, t]
    UP = unmixed(Pp, Cp, oppP); UL = unmixed(Pl, Cl, oppL)
    UPl = [tuple(x) for x in np.argwhere(np.triu(UP))]; ULl = [tuple(x) for x in np.argwhere(np.triu(UL))]
build_unmixed(nu)
print('unmixed pairs: points', len(UPl), 'lines', len(ULl), flush=True)

def total(sig):
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    nf = ~isfree
    rP = LM[sig][:, sig] & nf[:, None] & nf[None, :]; nfl = nf[sinv]; rL = PM[sinv][:, sinv] & nfl[:, None] & nfl[None, :]
    c0b = int((UP & ~rP).sum() // 2 + (UL & ~rL).sum() // 2)
    cov = lns.cover(F, sig, A)
    dd = sum(cp + cl for i, (p, l, cp, cl, h) in enumerate(d1.d1(F, sig)) if i in FD)
    return c0b + cov + dd, (c0b, cov, dd)

def step(sig, Sset, secs, seed):
    S = sorted(Sset); T = [int(sig[x]) for x in S]; inS = np.zeros(N, bool); inS[S] = True; inT = np.zeros(N, bool); inT[T] = True
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    m = cp_model.CpModel(); Y = {(x, L): m.NewBoolVar('') for x in S for L in T}
    for x in S: m.AddExactlyOne([Y[x, L] for L in T])
    for L in T: m.AddExactlyOne([Y[x, L] for x in S])
    hv = {}
    for x in S:
        for L in T: v = int(sig[x]) == L; m.AddHint(Y[x, L], v); hv[Y[x, L].Index()] = v
    soft = []
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
        xs = np.nonzero(PM[p] & ~isfree)[0]; const[PTS[sig[xs[~inS[xs]]]].ravel()] = True
        for w in LOF[p]:
            if isfreeL[w]: continue
            z = sinv[w]; us = sinv[LOF[z]]; ok = ~isfree[us] & ~inS[us]; const[us[ok]] = True
        for j in range(k):
            if A[i, j]: const[PTS[sig[F[j]]]] = True
        opp = ~PM[p]; opp[p] = False
        for u in np.nonzero(opp & ~const)[0]:
            u = int(u); lits = [Y[int(x), L] for x in xs[inS[xs]] for L in T if u in PTS[L]]
            if inS[u]:
                for w in LOF[p]:
                    if isfreeL[w]: continue
                    z = int(sinv[w]); lits += [Y[u, L] for L in T if z in PTS[L]]
            need(lits)
        l = int(sig[p]); const = np.zeros(N, bool)
        Ms = np.nonzero(LM[l] & ~isfreeL)[0]; Mf = Ms[~inT[Ms]]; const[LOF[sinv[Mf]].ravel()] = True; Mv = Ms[inT[Ms]]
        for y in PTS[l]:
            if isfree[y]: continue
            zs = PTS[sig[y]]
            for z in zs:
                if not isfree[z] and not inS[z]: const[sig[z]] = True
        for j in range(k):
            if A[j, i]: const[LOF[F[j]]] = True
        oppl = ~LM[l]; oppl[l] = False
        for mm in np.nonzero(oppl & ~const)[0]:
            mm = int(mm); lits = [Y[int(y), int(M)] for M in Mv for y in S if mm in LOF[y]]
            for y in PTS[l]:
                if isfree[y]: continue
                for z in PTS[sig[y]]:
                    z = int(z)
                    if not isfree[z] and inS[z] and inT[mm]: lits.append(Y[z, mm])
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
    # coset-0 routes for unmixed pairs touching S (points) or T (lines)
    ands = {}
    def AND(a, b):
        key = (a.Index(), b.Index())
        if key not in ands:
            v = m.NewBoolVar(''); m.AddImplication(v, a); m.AddImplication(v, b); ands[key] = v
            hv[v.Index()] = hv.get(a.Index(), False) and hv.get(b.Index(), False); m.AddHint(v, hv[v.Index()])
        return ands[key]
    for a, b in UPl:
        if isfree[a] or isfree[b]: continue
        if not inS[a] and not inS[b]:
            if not LM[sig[a], sig[b]]: soft.append(None)
            continue
        if inS[a] and inS[b]:
            need([AND(Y[a, L], Y[b, L2]) for L in T for L2 in T if LM[L, L2]])
        else:
            x, o = (a, b) if inS[a] else (b, a)
            need([Y[x, L] for L in T if LM[L, sig[o]]])
    for s_, t in ULl:
        ps, pt = int(sinv[s_]), int(sinv[t])
        if isfree[ps] or isfree[pt]: continue
        if not inT[s_] and not inT[t]:
            if not PM[ps, pt]: soft.append(None)
            continue
        if inT[s_] and inT[t]:
            need([AND(Y[x, s_], Y[w, t]) for x in S for w in S if PM[x, w]])
        else:
            L, o = (s_, pt) if inT[s_] else (t, ps)
            need([Y[x, L] for x in S if PM[x, o]])
    cv = [c for c in soft if c is not None]; forced = len(soft) - len(cv)
    m.Maximize(sum(cv))
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = secs; sol.parameters.num_workers = 1; sol.parameters.random_seed = seed
    r = sol.Solve(m)
    if r not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return None, None
    new = sig.copy()
    for x in S:
        for L in T:
            if sol.Value(Y[x, L]): new[x] = L
    return new, (len(cv) - sum(int(sol.Value(c)) for c in cv) + forced, len(cv), len(ands), sol.StatusName(r))

secs = float(os.environ.get('SECS', 600)); stp = float(os.environ.get('STEP', 20)); size = int(os.environ.get('SIZE', 50))
rng = random.Random(int(os.environ.get('SEED', 1)))
cur, parts = total(sig); print('start', cur, parts, flush=True)
sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
banned = isfree.copy()
for p in F: banned[sinv[LOF[p]]] = True; banned[PTS[sig[p]]] = True
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
    Sset = [x for x in dict.fromkeys(cand) if not banned[x]][:2 * size // 3]
    rest = [x for x in range(N) if not banned[x] and x not in set(Sset)]; rng.shuffle(rest)
    return Sset + rest[:size - len(Sset)], bp, bl
def write(sig):
    with open(out, 'w') as f:
        f.write(' '.join(tok[:4]) + ' %d\n' % cur + ' '.join(tok[5:7]) + '\n')
        f.write(' '.join(map(str, sig)) + '\n' + ' '.join(map(str, sig)) + '\n')
        f.write(' '.join(tok[7 + 2 * N:7 + 3 * N]) + '\n' + ' '.join(tok[7 + 3 * N:7 + 4 * N]) + '\n')
        f.write(' '.join(str(3 * v) for v in nu) + '\n')
if os.environ.get('FLIPS'):
    t0 = time.time()
    while cur > 0 and time.time() - t0 < secs:
        _, bp, bl = neigh(sig, size)
        if len(bp):
            a, b = [int(x) for x in bp[rng.randrange(len(bp))]]
            cs = [c for c in range(N) if PM[a, c] and PM[b, c]]; c = rng.choice(cs)
            L1 = [int(L) for L in LOF[a] if c in PTS[L]][0]; L2 = [int(L) for L in LOF[c] if b in PTS[L]][0]
            fl = rng.choice([(a, L1), (c, L1), (c, L2), (b, L2)])
        else:
            s_, t = [int(x) for x in bl[rng.randrange(len(bl))]]
            ys = [y for y in range(N) if LM[s_, y] and LM[y, t]] if False else [int(M) for M in range(N) if LM[s_, M] and LM[M, t]]
            M = rng.choice(ys); y1 = [int(y) for y in PTS[s_] if y in PTS[M]][0]; y2 = [int(y) for y in PTS[M] if y in PTS[t]][0]
            fl = rng.choice([(y1, s_), (y1, M), (y2, M), (y2, t)])
        if (fl[0], fl[1]) in dele: continue
        fi = fl[1] * 8 + [int(x) for x in PTS[fl[1]]].index(fl[0])
        nu_old = nu.copy(); sig_old = sig.copy(); cur_old = cur
        nu[fi] ^= 1; build_unmixed(nu)
        c1, p1 = total(sig); best = (c1, sig.copy())
        for r in range(int(os.environ.get('REPAIRS', 4))):
            if best[0] <= cur_old - 1 or best[0] == 0: break
            Sset, _, _ = neigh(best[1], size)
            new, info = step(best[1], Sset, stp, rng.randint(1, 10 ** 6))
            if new is None: continue
            c2, p2 = total(new)
            if c2 < best[0]: best = (c2, new)
        print('flip %d: after flip %d %s -> repaired %d (cur %d)' % (fi, c1, p1, best[0], cur_old), flush=True)
        if best[0] <= cur_old:
            sig, cur = best[1], best[0]; write(sig)
        else:
            nu[:] = nu_old; sig = sig_old; cur = cur_old; build_unmixed(nu)
t0 = time.time()
while cur > 0 and time.time() - t0 < secs:
    Sset, _, _ = neigh(sig, size)
    tb = time.time(); new, info = step(sig, Sset, stp, rng.randint(1, 10 ** 6))
    if new is None: print('no solution'); continue
    c2, p2 = total(new)
    print('|S| %d model %s exact %d %s (cur %d) %.1fs' % (len(Sset), info, c2, p2, cur, time.time() - tb), flush=True)
    if c2 <= cur:
        sig, cur = new, c2
        with open(out, 'w') as f:
            f.write(' '.join(tok[:4]) + ' %d\n' % cur + ' '.join(tok[5:7]) + '\n')
            f.write(' '.join(map(str, sig)) + '\n' + ' '.join(map(str, sig)) + '\n')
            f.write(' '.join(tok[7 + 2 * N:7 + 3 * N]) + '\n' + ' '.join(tok[7 + 3 * N:7 + 4 * N]) + '\n')
            f.write(' '.join(str(3 * v) for v in nu) + '\n')
print('final', cur, total(sig)[1])
