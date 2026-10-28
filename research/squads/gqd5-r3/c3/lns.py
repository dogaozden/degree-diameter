# LNS for the component packing (card r3c3): remove a random subset of the current state, solve the freed
# subproblem exactly (weighted MaxSAT via RC2) over all components whose lines are now free, accept if not worse.
# usage: lns.py START(json point list or 'sa:<file>') SEED ITERS KMIN KMAX OUT
import sys, json, random, time
import numpy as np
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c3')
from common import *

nl, nc, w, LN, pts = load_instance()
idx = {tuple(pts[c]): c for c in range(nc)}
Gw = W(9)

def state_from_points(P):
    Ps = set(P)
    nbc = {p: sum(1 for r in P if r != p and Gw.col[p, r]) for p in P}
    st = []
    done = set()
    for p in P:
        if p in done: continue
        if nbc[p] == 0:
            st.append(idx[(p,)]); done.add(p)
        elif nbc[p] == 1:
            r = [r for r in P if r != p and Gw.col[p, r]][0]
            st.append(idx[tuple(sorted((p, r)))]); done.add(p); done.add(r)
        else:
            raise ValueError("not relaxed")
    return sorted(set(st))

def owners(state):
    own = -np.ones(nl, dtype=np.int64)
    for c in state:
        for l in LN[c][LN[c] >= 0]: own[l] = c
    return own

def solve_sub(own, rng):
    free = own < 0
    cand = np.nonzero(np.all(np.where(LN >= 0, free[np.maximum(LN, 0)], True), axis=1))[0]
    cand = list(map(int, cand))
    if not cand: return []
    wcnf = WCNF()
    vid = {c: i + 1 for i, c in enumerate(cand)}
    bylines = {}
    for c in cand:
        for l in LN[c][LN[c] >= 0]:
            bylines.setdefault(int(l), []).append(vid[c])
    for l, vs in bylines.items():
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                wcnf.append([-vs[i], -vs[j]])
    for c in cand:
        wcnf.append([vid[c]], weight=1000 * int(w[c]) + rng.randrange(0, 10))
    rc = RC2(wcnf, solver='g4')
    model = rc.compute()
    rc.delete()
    inv = {v: c for c, v in vid.items()}
    return [inv[v] for v in model if v > 0 and v in inv]

def main():
    start, seed, iters, kmin, kmax, outf = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    rng = random.Random(seed)
    if start.startswith('sa:'):
        P = [int(x) for x in open(start[3:]).read().split()[1:]]
    else:
        P = json.load(open(start))
    state = state_from_points(P)
    cur = int(w[state].sum())
    best = cur; bestP = points_of(state, pts)
    print("start W", cur, "comps", len(state), flush=True)
    t0 = time.time(); last_imp = 0
    for it in range(iters):
        k = rng.randint(kmin, min(kmax, len(state)))
        rem = set(rng.sample(state, k))
        keep = [c for c in state if c not in rem]
        own = owners(keep)
        sol = solve_sub(own, rng)
        newstate = sorted(set(keep) | set(sol))
        nw = int(w[newstate].sum())
        if nw >= cur:
            state = newstate; cur = nw
        if cur > best:
            best = cur; bestP = points_of(state, pts); last_imp = it
            assert verify(bestP), "invalid"
            json.dump(bestP, open(outf, 'w'))
            print("it", it, "best", best, "time", round(time.time() - t0, 1), flush=True)
        if it % 200 == 0:
            print("it", it, "cur", cur, "best", best, "time", round(time.time() - t0, 1), flush=True)
    print("FINAL best", best, "points", len(bestP), flush=True)

if __name__ == '__main__':
    main()
