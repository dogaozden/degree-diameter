"""Exact orbit-union search for relaxed sets of W(11) invariant under a subgroup H of G (spread stabiliser).
Constraints (same as the point model, see research/squads/gqd5-r2/c2/sat_model.py): T is relaxed iff
 (a) no two points of T on one S-line, (b) for each p in T, at most one non-S neighbour of p is in T.
Both are 'not all of these points in T' constraints; under H they become 'not all of these orbits' clauses.
Usage: python3 orbsolve.py <cyclic subgroup index> <timeout-free>  (prints one JSON line)."""
import sys, json, time
import numpy as np
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
D = '/home/user/degree-diameter/research/squads/gqd5-r2/c2/'
S_ = json.load(open(D + 'struct.json'))
plines, lines, S, sline = S_['plines'], S_['lines'], set(S_['S']), np.array(S_['sline'])
n = len(plines)
S_pts = {}
for p in range(n): S_pts.setdefault(int(sline[p]), []).append(p)
nbr_nonS = []
for p in range(n):
    nb = [q for l in plines[p] if l not in S for q in lines[l] if q != p]
    nbr_nonS.append(np.array(nb, dtype=np.int64))
G = np.load('/home/user/degree-diameter/research/squads/gqd5-r3/c2/group.npy').astype(np.int64)

def orbit_ids(gens):
    lab = -np.ones(n, dtype=np.int64); k = 0
    for s in range(n):
        if lab[s] >= 0: continue
        stack = [s]; lab[s] = k
        while stack:
            x = stack.pop()
            for g in gens:
                y = g[x]
                if lab[y] < 0:
                    lab[y] = k; stack.append(y)
        k += 1
    return lab, k

def build_wcnf(lab, k):
    size = np.bincount(lab, minlength=k)
    hard = set()
    # (a) S-lines
    for l, pts in S_pts.items():
        cnt = {}
        for p in pts: cnt[int(lab[p])] = cnt.get(int(lab[p]), 0) + 1
        o = sorted(cnt)
        for x in o:
            if cnt[x] >= 2: hard.add((x,))
        for i in range(len(o)):
            for j in range(i + 1, len(o)):
                hard.add((o[i], o[j]))
    # (b) one representative per orbit suffices (clause set is H-invariant)
    reps = {}
    for p in range(n): reps.setdefault(int(lab[p]), p)
    for O, r in reps.items():
        nb = nbr_nonS[r]
        ids = lab[nb]
        # pairs of non-S neighbours of r (all pairs), each with the orbit of r
        m = len(nb)
        iu, ju = np.triu_indices(m, 1)
        a = np.full(iu.shape, O, dtype=np.int64); b = ids[iu]; c = ids[ju]
        T = np.stack([a, b, c], axis=1)
        T.sort(axis=1)
        # collapse repeated entries: a clause is the SET of orbits
        for row in np.unique(T, axis=0):
            s = tuple(sorted(set(row.tolist())))
            hard.add(s)
    # keep only minimal clauses (drop supersets of a unit/pair clause)
    units = {c[0] for c in hard if len(c) == 1}
    clauses = set()
    for c in hard:
        if len(c) == 1 or not (set(c) & units):
            clauses.add(c)
    # drop 3-clauses containing a 2-clause subset
    pairs = {c for c in clauses if len(c) == 2}
    final = []
    for c in clauses:
        if len(c) == 3 and any(tuple(x) in pairs for x in [(c[0], c[1]), (c[0], c[2]), (c[1], c[2])]):
            continue
        final.append(c)
    w = WCNF()
    for c in final:
        w.append([-(x + 1) for x in c])
    for O in range(k):
        if O in units: continue
        w.append([O + 1], weight=int(size[O]))
    return w, size, len(final), len(units)

def solve(gens, tlimit=60.0, hint=None):
    """CP-SAT (single worker) on the orbit-level model. Returns optimum or best found with the proven bound."""
    from ortools.sat.python import cp_model
    t0 = time.time()
    lab, k = orbit_ids(gens)
    w, size, nclauses, nunits = build_wcnf(lab, k)
    t1 = time.time()
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f'x{O}') for O in range(k)]
    units = set()
    for cl in w.hard:
        lits = [-l - 0 for l in cl]
        if len(cl) == 1: units.add(-cl[0] - 1)
        m.AddBoolOr([x[abs(l) - 1].Not() for l in cl])
    m.Maximize(sum(int(size[O]) * x[O] for O in range(k)))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = tlimit
    s.parameters.num_workers = 1
    st = s.Solve(m)
    sel = {O for O in range(k) if s.Value(x[O])} if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else set()
    T = sorted(p for p in range(n) if int(lab[p]) in sel)
    return dict(norb=k, nclauses=nclauses, forced0=nunits, build_s=round(t1 - t0, 1), solve_s=round(time.time() - t1, 1),
                status=s.StatusName(st), opt=int(sum(size[O] for O in sel)), bound=s.BestObjectiveBound(),
                T=T, orbit_sizes=sorted(set(size.tolist())))

if __name__ == '__main__':
    import subprocess
    if sys.argv[1] == 'cyc':
        idx = int(sys.argv[2])
        cyc = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_subgroups.json'))
        g = G[cyc[idx]['gen']]
        res = solve([g]); res['order'] = cyc[idx]['order']; res['idx'] = idx
    print(json.dumps({k: v for k, v in res.items() if k != 'T'} | {'T_len': len(res['T'])}))
