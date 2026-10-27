"""c4 (hexfam_r2) core: orbit unions of subgroups of W(E7) mod 13 and G2/SL3 subgroups on H(13).
Orbit-level exact max-weight clique (time-limited) + orbit-level iterated local search (ILS) on the compat graph."""
import sys, time, os, subprocess, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from lib import orbit_labels, orbit_members, reflection_matrix
from q6lib import Geo, A7, inv_mod
from e7roots import e7_roots, subsystem
from mwc import max_weight_clique
Q = 13; CAP = Q ** 3 + 1
POV = '/home/user/degree-diameter/research/projects/hexagon-family/tools/povcheck'
HEXB = '/home/user/degree-diameter/research/projects/hexagon-family/hex/hex_q13.bin'

_G = None
def geo():
    global _G
    if _G is None: _G = Geo(Q)
    return _G

def orbits_of(perms):
    G = geo()
    lab = orbit_labels(G.N, perms)
    members, counts = orbit_members(lab)
    return members, counts

def sc_compat(members, cap=CAP):
    """self-compatible orbits (pairwise opposite inside the orbit; rep vs all = enough) and compat matrix."""
    G = geo(); q = G.q; C = G.C
    S = []
    for o, m in enumerate(members):
        if len(m) > cap or len(m) == 0: continue
        r = m[0]
        ok = ((C[r] @ A7 @ C[m].T) % q) != 0
        ok[0] = True
        if ok.all(): S.append(o)
    n = len(S)
    if n == 0: return S, np.zeros((0, 0), bool)
    sizes = np.array([len(members[o]) for o in S])
    order = np.concatenate([members[o] for o in S])
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    A = np.zeros((n, n), bool)
    for a, o in enumerate(S):
        r = members[o][0]
        ok = ((C[r] @ A7 @ C[order].T) % q) != 0
        A[a] = np.logical_and.reduceat(ok, starts)
    A = A & A.T
    np.fill_diagonal(A, False)
    return S, A

def exact_clique(w, A, tl):
    n = len(w); adj = [0] * n
    for i in range(n):
        bits = 0
        for j in np.nonzero(A[i])[0]: bits |= 1 << int(j)
        adj[i] = bits
    wgt, verts, done = max_weight_clique(w, adj, tl)
    return wgt, list(verts), done

def ils(w, A, tl, seed=1, init=None):
    """orbit-level ILS for max-weight clique in compat graph A (conflict = not A).
    moves: greedy add of free vertices; (1,1)-swap when a vertex conflicts with one member and is heavier;
    perturbation: force-insert a random vertex (drop its conflicts) and restart descent; keep best."""
    rng = np.random.default_rng(seed)
    n = len(w); w = np.asarray(w, dtype=np.int64)
    if n == 0: return 0, []
    conf = ~A.copy(); np.fill_diagonal(conf, False)
    confi = conf.astype(np.int32)
    inS = np.zeros(n, bool); cc = np.zeros(n, np.int32)
    cur = 0
    def add(v):
        nonlocal cur
        inS[v] = True; cc[:] += confi[v]; cur += w[v]
    def drop(v):
        nonlocal cur
        inS[v] = False; cc[:] -= confi[v]; cur -= w[v]
    def descend():
        while True:
            free = np.nonzero((~inS) & (cc == 0))[0]
            if len(free):
                v = free[np.argmax(w[free] + rng.random(len(free)) * 0.5)]
                add(v); continue
            # (1,1) swap: candidates with exactly one conflicting member, heavier than it
            cand = np.nonzero((~inS) & (cc == 1))[0]
            if len(cand):
                done = False
                rng.shuffle(cand)
                for v in cand:
                    us = np.nonzero(inS & conf[v])[0]
                    if len(us) == 1 and w[v] > w[us[0]]:
                        drop(us[0]); add(v); done = True; break
                if done: continue
            return
    best = cur_best = 0; bestS = []
    if init:
        for v in init:
            if cc[v] == 0 and not inS[v]: add(v)
    descend()
    best, bestS = cur, np.nonzero(inS)[0].tolist()
    t0 = time.time(); it = 0
    while time.time() - t0 < tl:
        it += 1
        v = rng.integers(n)
        if inS[v]: continue
        # force insert v
        us = np.nonzero(inS & conf[v])[0]
        saved = np.nonzero(inS)[0]
        for u in us: drop(u)
        add(v)
        descend()
        if cur > best:
            best, bestS = cur, np.nonzero(inS)[0].tolist()
        elif cur < best - max(1, 0.02 * best) and rng.random() < 0.7:
            # restart from best with prob
            for u in np.nonzero(inS)[0]: drop(u)
            for u in bestS: add(u)
    return int(best), bestS

def write_set(name, pts):
    fn = os.path.join(HERE, name)
    open(fn, 'w').write('\n'.join(map(str, sorted(int(p) for p in pts))) + '\n')
    return fn

def score(path):
    out = subprocess.run([POV, HEXB, path], capture_output=True, text=True, timeout=600).stdout.strip().splitlines()
    return out[-1] if out else 'ERR'

def union_pts(members, orbit_ids):
    return [int(p) for o in orbit_ids for p in members[o]]

def solve_orbits(label, perms, tl_exact=60, tl_ils=60, seed=1, verbose=True):
    """orbit union search for a group given by point permutations. returns (best weight, points, info)"""
    t0 = time.time()
    members, counts = orbits_of(perms)
    S, A = sc_compat(members)
    info = dict(label=label, orbits=len(members), selfcompat=len(S))
    if len(S) == 0:
        info.update(best=0, method='none')
        return 0, [], info
    w = [len(members[o]) for o in S]
    wgt_e, cl_e, done = exact_clique(w, A, tl_exact)
    best, cl = wgt_e, cl_e
    method = 'exact' if done else 'exact-timelimit'
    if not done and tl_ils > 0:
        wgt_i, cl_i = ils(w, A, tl_ils, seed=seed, init=cl_e)
        if wgt_i > best:
            best, cl = wgt_i, cl_i; method = 'ils'
    pts = union_pts(members, [S[i] for i in cl])
    info.update(best=best, method=method, exact_done=bool(done), secs=round(time.time() - t0, 1),
                sizes=sorted(int(counts[S[i]]) for i in cl)[::-1][:20])
    if verbose: print(info, flush=True)
    return best, pts, info

def refl_perms(roots_basis):
    G = geo()
    return [G.perm(reflection_matrix(b, Q)) for b in roots_basis]
