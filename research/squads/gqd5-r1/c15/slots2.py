"""Vectorised search. Candidates = (tournament, typing). Value at grid point p = min_v OUT_v.p + min_v IN_v.p."""
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
from slots import forms

def build(n, tournaments):
    r = (n - 1) // 2
    types = ((np.arange(1 << n)[:, None] >> np.arange(n)[None, :]) & 1).astype(np.int8)
    OUTs, INs, tids, typs = [], [], [], []
    for tid, A in enumerate(tournaments):
        OUT, IN = forms(A, types, r)
        OUTs.append(OUT.astype(np.int8)); INs.append(IN.astype(np.int8))
        tids.append(np.full(len(types), tid, dtype=np.int32)); typs.append(np.arange(len(types), dtype=np.int32))
    return np.concatenate(OUTs), np.concatenate(INs), np.concatenate(tids), np.concatenate(typs), types

def values(OUT, IN, P):
    Pf = P.astype(np.float32)
    Kb = np.einsum('ncd,gd->ncg', OUT.astype(np.float32), Pf).min(axis=1)
    Ka = np.einsum('ncd,gd->ncg', IN.astype(np.float32), Pf).min(axis=1)
    return Kb + Ka

def search(n, tournaments, P, chunk=4000, eps=1e-3):
    OUTa, INa, tida, typa, types = build(n, tournaments)
    N = len(OUTa); G = len(P)
    best = np.full(G, -1e9)
    for s in range(0, N, chunk):
        best = np.maximum(best, values(OUTa[s:s+chunk], INa[s:s+chunk], P).max(axis=0))
    forms_at = [dict() for _ in range(G)]
    for s in range(0, N, chunk):
        O = OUTa[s:s+chunk]; I = INa[s:s+chunk]
        v = values(O, I, P)
        for g in range(G):
            idx = np.where(v[:, g] >= best[g] - eps)[0]
            if len(idx) == 0: continue
            p = P[g].astype(np.float64)
            ob = O[idx].astype(np.float64) @ p; ia = I[idx].astype(np.float64) @ p
            tb = ob <= ob.min(axis=1, keepdims=True) + 1e-6
            ta = ia <= ia.min(axis=1, keepdims=True) + 1e-6
            for vv in range(n):
                for uu in range(n):
                    m = tb[:, vv] & ta[:, uu]
                    if not m.any(): continue
                    sel = idx[m]
                    F = O[sel, vv].astype(int) + I[sel, uu].astype(int)
                    U, first = np.unique(F, axis=0, return_index=True)
                    for f, k in zip(map(tuple, U), first):
                        if f not in forms_at[g]:
                            forms_at[g][f] = s + int(sel[k])
    return best, forms_at, OUTa, INa, tida, typa, types

def describe(tournaments, n, tida, typa, types, gi):
    A = tournaments[tida[gi]]
    arcs = [(int(u), int(v)) for u in range(n) for v in range(n) if A[u, v]]
    typ = ''.join('HD'[x] for x in types[typa[gi]])
    return arcs, typ
