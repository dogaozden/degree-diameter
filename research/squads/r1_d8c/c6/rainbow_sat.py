"""c6: bundle-rainbow hexagon voltages in Z_k on I(H(q)) by SAT (CEGAR over apartments).

Equivalence used: the q+1 geodesics between opposite elements carry distinct voltages iff every 12-cycle
(apartment) has nonzero net voltage (any two geodesics of a bundle form an apartment; girth 12).
Voltage convention: dart point->line has +a, line->point has -a; spanning tree (point 0 BFS tree) fixed to 0.
Usage: python3 rainbow_sat.py q k seed budget_seconds
"""
import sys, time, random, threading
import numpy as np
from collections import deque
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load
from pysat.solvers import Solver

q, k, seed, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
random.seed(seed)
N, LP, PL, coord = load(q)
# incidence graph: point p -> vertex p, line l -> vertex N+l
adj = [[] for _ in range(2 * N)]
for l in range(N):
    for p in LP[l]:
        adj[p].append(N + l)
        adj[N + l].append(int(p))
eid = {}
E = 0
for l in range(N):
    for p in LP[l]:
        eid[(int(p), l)] = E
        E += 1

# spanning tree from vertex 0 (BFS), tree edges fixed to 0
tree = set()
seen = [False] * (2 * N)
seen[0] = True
dq = deque([0])
while dq:
    v = dq.popleft()
    for w in adj[v]:
        if not seen[w]:
            seen[w] = True
            tree.add((min(v, w), max(v, w)))
            dq.append(w)
def edge_of(v, w):
    p, l = (v, w - N) if v < N else (w, v - N)
    return eid[(p, l)]
tree_eids = set(edge_of(a, b) for a, b in tree)
nontree = [e for e in range(E) if e not in tree_eids]
nt_index = {e: i for i, e in enumerate(nontree)}
print(f"q={q} N={N} edges={E} tree={len(tree_eids)} nontree={len(nontree)} k={k}", flush=True)

# enumerate apartments via geodesic bundles from point sources (x<y), dedupe by edge set
apts = {}
t0 = time.time()
for x in range(N):
    dist = [-1] * (2 * N)
    par = [[] for _ in range(2 * N)]
    dist[x] = 0
    dq = deque([x])
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if dist[w] == -1:
                dist[w] = dist[v] + 1
                dq.append(w)
            if dist[w] == dist[v] + 1:
                par[w].append(v)
    for y in range(x + 1, N):
        if dist[y] != 6:
            continue
        # enumerate all geodesics x -> y (backwards from y)
        paths = []
        def back(v, acc):
            if v == x:
                paths.append(acc[::-1])
                return
            for u in par[v]:
                back(u, acc + [u])
        back(y, [y])
        assert len(paths) == q + 1, (x, y, len(paths))
        for i in range(len(paths)):
            for j in range(i + 1, len(paths)):
                cyc = paths[i] + paths[j][-2:0:-1]  # x..y then y..x without endpoints
                assert len(cyc) == 12
                es = [edge_of(cyc[t], cyc[(t + 1) % 12]) for t in range(12)]
                sg = [1 if cyc[t] < N else -1 for t in range(12)]  # dart from point gets +
                key = tuple(sorted(es))
                if key not in apts:
                    apts[key] = (es, sg)
print(f"apartments={len(apts)} enum_time={time.time()-t0:.1f}s", flush=True)
A = list(apts.values())
M = len(A)
# arrays: for each apartment, nontree edge positions (or -1) and signs
maxlen = 12
IDX = np.full((M, maxlen), E, dtype=np.int64)  # E = dummy zero column
SGN = np.zeros((M, maxlen), dtype=np.int64)
for a, (es, sg) in enumerate(A):
    for t, (e, s) in enumerate(zip(es, sg)):
        IDX[a, t] = e if e not in tree_eids else E
        SGN[a, t] = s

# SAT encoding
NT = len(nontree)
def xvar(e, t):  # one-hot var for nontree edge e value t
    return 1 + nt_index[e] * k + t
nxt = [1 + NT * k]
def newv():
    nxt[0] += 1
    return nxt[0] - 1
solver = Solver(name='g4')
for e in nontree:
    lits = [xvar(e, t) for t in range(k)]
    solver.add_clause(lits)
    for i in range(k):
        for j in range(i + 1, k):
            solver.add_clause([-lits[i], -lits[j]])
# fix gauge: nothing (tree edges are simply 0)

def add_apartment(a):
    es, sg = A[a]
    seq = [(e, s) for e, s in zip(es, sg) if e not in tree_eids]
    m = len(seq)
    if m == 0:
        return False
    # partial sums P_1..P_{m-1} one-hot; forbid final sum == 0
    prev = None  # None means constant 0
    for j in range(m):
        e, s = seq[j]
        if j == m - 1:
            if prev is None:
                # single nontree edge: value s*t != 0
                for t in range(k):
                    if (s * t) % k == 0:
                        solver.add_clause([-xvar(e, t)])
            else:
                for u in range(k):
                    for t in range(k):
                        if (u + s * t) % k == 0:
                            solver.add_clause([-prev[u], -xvar(e, t)])
            break
        cur = [newv() for _ in range(k)]
        for u in range(k):
            for t in range(k):
                val = (s * t) % k if prev is None else (u + s * t) % k
                if prev is None and u > 0:
                    continue
                cl = [-xvar(e, t), cur[val]]
                if prev is not None:
                    cl.append(-prev[u])
                solver.add_clause(cl)
        # at most one of cur (exactly one is forced by premises)
        for i in range(k):
            for j2 in range(i + 1, k):
                solver.add_clause([-cur[i], -cur[j2]])
        prev = cur
    return True

def model_values(model):
    val = np.zeros(E + 1, dtype=np.int64)
    ms = set(l for l in model if l > 0)
    for e in nontree:
        for t in range(k):
            if xvar(e, t) in ms:
                val[e] = t
                break
    return val

def violated(val):
    S = (val[IDX] * SGN).sum(axis=1) % k
    return np.nonzero(S == 0)[0]

# initial batch
order = list(range(M))
random.shuffle(order)
added = set()
for a in order[:3000]:
    add_apartment(a); added.add(a)
rounds = 0
status = None
while True:
    rounds += 1
    if time.time() - t0 > budget:
        status = 'TIMEOUT'
        break
    tm = threading.Timer(max(5.0, budget - (time.time() - t0)), solver.interrupt)
    tm.start()
    ok = solver.solve_limited(expect_interrupt=True)
    tm.cancel()
    if ok is None:
        status = 'TIMEOUT'
        break
    if not ok:
        status = 'UNSAT'
        break
    val = model_values(solver.get_model())
    bad = violated(val)
    print(f"round {rounds}: clauses-apartments={len(added)} violated={len(bad)} t={time.time()-t0:.0f}s", flush=True)
    if len(bad) == 0:
        status = 'SAT'
        break
    random.shuffle(bad)
    for a in bad[:4000]:
        if a not in added:
            add_apartment(int(a)); added.add(int(a))

print("STATUS", status, flush=True)
if status == 'SAT':
    val = model_values(solver.get_model())
    # independent exact check: every opposite pair has q+1 geodesics with pairwise distinct sums
    fn = f'/home/user/degree-diameter/research/squads/r1_d8c/c6/volt_q{q}_k{k}_s{seed}.txt'
    with open(fn, 'w') as f:
        f.write(f"{q} {k}\n")
        for e in range(E):
            p = None
    # full check via geodesic enumeration
    bad_pairs = 0
    checked = 0
    def vtx_val(path):
        s = 0
        for t in range(len(path) - 1):
            a, b = path[t], path[t + 1]
            if a < N:
                s += (val[eid[(a, b - N)]] if e_not_tree(a, b) else 0)
            else:
                s -= (val[eid[(b, a - N)]] if e_not_tree(a, b) else 0)
        return s % k
    def e_not_tree(a, b):
        return edge_of(a, b) not in tree_eids
    for x in range(0, N):
        dist = [-1] * (2 * N); par = [[] for _ in range(2 * N)]
        dist[x] = 0; dq = deque([x])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] == -1:
                    dist[w] = dist[v] + 1; dq.append(w)
                if dist[w] == dist[v] + 1:
                    par[w].append(v)
        for y in range(N):
            if dist[y] != 6 or y <= x and False:
                continue
            paths = []
            def back2(v, acc):
                if v == x:
                    paths.append(acc[::-1]); return
                for u in par[v]:
                    back2(u, acc + [u])
            back2(y, [y])
            sums = [vtx_val(p) for p in paths]
            checked += 1
            if len(set(sums)) != len(sums):
                bad_pairs += 1
    print(f"exact check: opposite point pairs checked={checked} bad={bad_pairs}", flush=True)
    with open(fn, 'w') as f:
        f.write(f"Z {k}\n")
        f.write(" ".join(str(int(val[e])) for e in range(E)) + "\n")
    print("wrote", fn)
