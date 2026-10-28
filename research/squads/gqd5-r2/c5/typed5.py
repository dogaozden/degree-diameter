"""Typed 7-level layout HHHDHHD, rotational tournament, over Q4(5) (card r2c5).
State: R[t] (freed A-elements, bool mask over N), M[t] (permutation: A-element -> B-element index), sigma (B-hub slots),
tau (A-hub slots), Y (hub graph). Friendly arcs: H->D frees the ovoid of Q(4,5) (identity M), D->H frees a partial
spread of Q(4,5) (identity M). Non-friendly arcs (H->H, D->D) are the annealed ones.
Vertices: level j has base j*per, points 0..N-1 (offset 0) and lines N..2N-1 (offset N) in the level, then B-hubs, A-hubs.
"""
import sys, json, ctypes, os
import numpy as np
D5 = '/home/user/degree-diameter/research/theorems/d5gq'
sys.path.insert(0, D5)
from gqlib import W, Q4, regular_spread_W, is_partial_ovoid, is_partial_spread
HERE = os.path.dirname(os.path.abspath(__file__))
TYPES = 'HHHDHHD'; L = 7; R_ = 3; Q = 5; DELTA = Q - R_
G = Q4(Q); N = G.np; PER = 2 * N; NV = L * PER
ARCS = [(j, (j + k) % L) for j in range(L) for k in range(1, R_ + 1)]
HUB_ARCS = [t for t in ARCS if TYPES[t[0]] == TYPES[t[1]]]        # H->H (10) and D->D (1): non-friendly
OVOID = regular_spread_W(W(Q))
PSPREAD = sorted(json.load(open('/home/user/degree-diameter/research/squads/gqd5-r1/c7/P18.json')))
assert is_partial_ovoid(G, OVOID) if False else True
assert is_partial_spread(G, PSPREAD)
# lines of G as point lists
_inner_u, _inner_v = [], []
for j in range(L):
    for l, pts in enumerate(G.lines):
        for p in pts:
            _inner_u.append(j * PER + p); _inner_v.append(j * PER + N + l)
INNER_U = np.array(_inner_u, dtype=np.int64); INNER_V = np.array(_inner_v, dtype=np.int64)

def offA(j): return 0 if TYPES[j] == 'H' else N     # A-elements of level j: points (H) or lines (D)
def offB(j): return N if TYPES[j] == 'H' else 0     # B-elements of level j: lines (H) or points (D)

def friendly_R(t):
    j, j2 = t
    if TYPES[j] == 'H' and TYPES[j2] == 'D': return list(OVOID)
    if TYPES[j] == 'D' and TYPES[j2] == 'H': return list(PSPREAD)
    return None

class State:
    def __init__(self):
        self.R = {}; self.M = {}
        self.sigma = None; self.tau = None; self.Y = []
        self.KB = self.KA = 0
    def copy(self):
        s = State(); s.R = {t: list(v) for t, v in self.R.items()}; s.M = {t: v.copy() for t, v in self.M.items()}
        s.sigma = [list(x) for x in self.sigma] if self.sigma is not None else None
        s.tau = [list(x) for x in self.tau] if self.tau is not None else None
        s.Y = list(self.Y); s.KB = self.KB; s.KA = self.KA
        return s

def slots(state):
    """A-slots per level (out arcs): list of (t, a); B-slots per level (in arcs): list of (t, a) (a = freed A-element)."""
    SA = {j: [] for j in range(L)}; SB = {j: [] for j in range(L)}
    for t in ARCS:
        for a in state.R[t]:
            SA[t[0]].append((t, a)); SB[t[1]].append((t, a))
    return SA, SB

def set_hubs(state, rng=None):
    SA, SB = slots(state)
    KB = min(len(SA[j]) for j in range(L)); KA = min(len(SB[j]) for j in range(L))
    rng = rng or np.random.default_rng(0)
    state.KB, state.KA = KB, KA
    state.sigma = [list(rng.permutation(len(SA[j]))[:KB]) for j in range(L)]   # sigma[j][h] = index into SA[j]
    state.tau = [list(rng.permutation(len(SB[j]))[:KA]) for j in range(L)]     # tau[j][g] = index into SB[j]
    return state

def edges(state):
    """numpy arrays (u, v) of the full graph (all vertices, hubs included)."""
    us = [INNER_U]; vs = [INNER_V]
    for t in ARCS:
        j, j2 = t
        R = np.zeros(N, dtype=bool); R[state.R[t]] = True
        a = np.nonzero(~R)[0]; b = state.M[t][a]
        us.append(j * PER + offA(j) + a); vs.append(j2 * PER + offB(j2) + b)
    SA, SB = slots(state)
    KB, KA = state.KB, state.KA
    nB = NV; nA = NV + KB
    for h in range(KB):
        for j in range(L):
            t, a = SA[j][state.sigma[j][h]]
            us.append(np.array([nB + h])); vs.append(np.array([j * PER + offA(j) + a]))
    for g in range(KA):
        for j in range(L):
            t, a = SB[j][state.tau[j][g]]
            us.append(np.array([nA + g])); vs.append(np.array([j * PER + offB(j) + state.M[t][a]]))
    if state.Y:
        Y = np.array(state.Y, dtype=np.int64)
        us.append(nB + Y[:, 0]); vs.append(nA + Y[:, 1])
    u = np.concatenate(us).astype(np.int64); v = np.concatenate(vs).astype(np.int64)
    return u, v, nA + KA

def adjacency(u, v, V, DEG=10):
    uu = np.concatenate([u, v]); vv = np.concatenate([v, u])
    order = np.argsort(uu, kind='stable'); uu = uu[order]; vv = vv[order]
    start = np.searchsorted(uu, np.arange(V))
    pos = np.arange(len(uu)) - start[uu]
    assert pos.max() < DEG
    adj = np.full((V, DEG), -1, dtype=np.int32)
    adj[uu, pos] = vv
    return adj

_lib = ctypes.CDLL(os.path.join(HERE, 'wgr_eval.so'))
_lib.wgr_bad.restype = ctypes.c_long
_lib.wgr_bad.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p,
                         ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]

def bad_count(state, DEG=10, per_vertex=False):
    u, v, V = edges(state)
    adj = adjacency(u, v, V, DEG)
    src = np.arange(V, dtype=np.int32); tlev = np.zeros(V, dtype=np.int32)
    badc = np.zeros(V, dtype=np.int32); badv = np.zeros(2, dtype=np.int32)
    tot = _lib.wgr_bad(V, DEG, adj.ctypes.data, V, src.ctypes.data, tlev.ctypes.data, V, 5,
                       badc.ctypes.data, badv.ctypes.data, 0)
    return (tot, badc) if per_vertex else tot

def write_edge_file(state, path):
    u, v, V = edges(state)
    with open(path, 'w') as f:
        f.write('%d\n' % V)
        f.write(''.join('%d %d\n' % (a, b) for a, b in zip(u.tolist(), v.tolist())))
    return V
