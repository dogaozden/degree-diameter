#!/usr/bin/env python3
# c46: anatomy of near misses + girth-restricted tabu search for Haar graphs H(G,S), S = {e,x,y,z}.
# Lift convention: (A,x) ~ (B, x*s) for s in S. Cost = uncovered vertices from both roots (= lift cost).
import sys, os, time, random, subprocess
from collections import deque
import numpy as np
T = '/home/user/degree-diameter/research/squads/b48/tools'
sys.path.insert(0, T)
import groups
HERE = '/home/user/degree-diameter/research/squads/b48/r1/c46'
DIPOLE = T + '/bases/dipole4.txt'

def setup(spec):
    global TBL, INV, N, GSPEC, LSPEC
    TBL = np.asarray(groups.table(spec)).astype(np.int32)
    N = TBL.shape[0]
    INV = np.argmax(TBL == 0, axis=1).astype(np.int32)
    GSPEC = spec

def walk_levels(L):
    # NB walks from a root: level t has 4*3^(t-1) walks; each gives (parent index in level t-1, edge index)
    lv = []; prev_last = [-1]
    for t in range(1, L + 1):
        par = []; edg = []; last = []
        for p, l in enumerate(prev_last):
            for e in range(4):
                if e != l:
                    par.append(p); edg.append(e)
        lv.append((np.array(par), np.array(edg)))
        prev_last = edg
    return lv

LV = walk_levels(8)

def dfs(S, Sinv, L, fwd_first=True):
    # returns list out[t] of shape (M, c_t) group values of NB walks of length t from root
    M = S.shape[0]
    prev = np.zeros((M, 1), dtype=np.int32)
    out = [prev]
    for t in range(1, L + 1):
        par, edg = LV[t - 1]
        V = S if ((t % 2 == 1) == fwd_first) else Sinv
        vals = TBL[prev[:, par], V[:, edg]]
        out.append(vals); prev = vals
    return out

def girth_viol(S, chunk=4000):
    # number of closed NB walks of length 4 and 6 from the A-root (=> 4-/6-cycles; G is transitive on A)
    res = np.zeros(S.shape[0], dtype=np.int64)
    for i in range(0, S.shape[0], chunk):
        Sc = S[i:i + chunk]; Si = INV[Sc]
        out = dfs(Sc, Si, 6)
        res[i:i + chunk] = (out[4] == 0).sum(1) + (out[6] == 0).sum(1)
    return res

def coverage(S, Sinv_=None):
    # cost from A-root and B-root; returns (cost_A, cost_B, list of per-level stats for row 0 if M==1)
    Si = INV[S]
    tot = []
    for root_fwd in (True, False):
        out = dfs(S, Si, 8, fwd_first=root_fwd)
        cov = []
        for m in range(S.shape[0]):
            even = np.unique(np.concatenate([out[t][m] for t in (0, 2, 4, 6, 8)]))
            odd = np.unique(np.concatenate([out[t][m] for t in (1, 3, 5, 7)]))
            cov.append((N - len(even)) + (N - len(odd)))
        tot.append(np.array(cov))
    return tot[0], tot[1]

def lift_cost(S):
    inp = '\n'.join(' '.join(str(int(v)) for v in row) for row in S) + '\n'
    r = subprocess.run([T + '/lift', DIPOLE, GSPEC.replace(' ', ':'), '4', '8', 'eval'],
                       input=inp, capture_output=True, text=True, timeout=110)
    vals = []
    for line in r.stdout.split('\n'):
        if line.strip() == '':
            continue
        vals.append(int(line) if line.strip().isdigit() else 999)
    return np.array(vals)

def write_edges(S, path):
    # lift edge list: (A,x) -> x, (B,y) -> N+y ; edges x ~ N + x*s
    with open(path, 'w') as f:
        f.write('%d\n' % (2 * N))
        for s in S:
            for x in range(N):
                f.write('%d %d\n' % (x, N + int(TBL[x, s])))

def level_stats(S):
    # per-level: walks, new distinct values on same side, duplicates (waste), closed walks
    out = dfs(S[None, :], INV[S][None, :], 8)[0:] if False else None
    Sv = np.array([S], dtype=np.int32); Si = INV[Sv]
    out = dfs(Sv, Si, 8)
    seen = {0: set([0]), 1: set()}
    rows = []
    for t in range(1, 9):
        vals = out[t][0]
        side = t % 2  # 1 = B side, 0 = A side
        key = side
        s_prev = seen.setdefault(key, set())
        new = set(vals.tolist()) - s_prev
        walks = len(vals)
        closed = int((vals == 0).sum()) if side == 0 else 0
        rows.append((t, walks, len(new), walks - len(new), closed))
        s_prev |= set(vals.tolist())
    return rows

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'check':
        setup('meta 55 20 2')
        S = np.array([[0, 929, 1084, 684]], dtype=np.int32)
        ca, cb = coverage(S)
        print('check meta55 near state: my cost A-root', ca[0], 'B-root', cb[0], 'lift eval', lift_cost(S)[0])
        for r in level_stats(S[0]):
            print('level t=%d walks=%d new_distinct=%d waste=%d closed=%d' % r)
