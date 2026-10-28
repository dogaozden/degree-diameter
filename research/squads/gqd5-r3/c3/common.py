# Shared helpers for card r3c3: component instance, state <-> point sets, verification.
import sys, json
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W

HERE = '/home/user/degree-diameter/research/squads/gqd5-r3/c3/'

def load_instance():
    lines = open(HERE + 'comps_W9.txt').read().split('\n')
    nl, nc = map(int, lines[0].split())
    w = np.zeros(nc, dtype=np.int64); LN = np.full((nc, 19), -1, dtype=np.int64)
    pts = []
    for c in range(nc):
        a = list(map(int, lines[c + 1].split()))
        wc, m = a[0], a[1]
        LN[c, :m] = a[2:2 + m]
        k = a[2 + m]
        pts.append(a[3 + m:3 + m + k])
        w[c] = wc
    return nl, nc, w, LN, pts

def points_of(state, pts):
    P = sorted(p for c in state for p in pts[c])
    return P

def verify(P):
    G = W(9)
    S = set(regular_spread_W(G))
    T = sorted(P)
    assert len(set(T)) == len(T)
    Ts = set(T)
    ok = True
    for p in T:
        nb = [r for L in G.plines[p] for r in G.lines[L] if r != p and r in Ts]
        if len(nb) > 1: ok = False
    for i, p in enumerate(T):
        for r in T[i + 1:]:
            if G.col[p, r]:
                L = [L for L in G.plines[p] if r in G.lines[L]][0]
                if L in S: ok = False
    return ok
