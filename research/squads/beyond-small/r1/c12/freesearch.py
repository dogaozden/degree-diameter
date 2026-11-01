# Random elements of <monomial, unipotent collineations>; keep cyclic free subgroups; quotient and check diameter.
import sys, pickle, random, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond-small/r1/c12')
from hexlib import Hex, orbit_quotient
q = int(sys.argv[1]); hx = Hex(f'hex/hex_q{q}.bin'); N, L = hx.N, hx.L
mono = pickle.load(open(f'monomial_q{q}.pkl', 'rb'))
unip = pickle.load(open(f'unip_q{q}.pkl', 'rb'))
gens = [(a.astype(np.int64), b.astype(np.int64)) for a, b, _ in mono + unip]
gens = [g for g in gens if not np.array_equal(g[0], np.arange(N))]
print('generators', len(gens), flush=True)
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
idp, idl = np.arange(N), np.arange(L)
def mul(a, b):  # (a after b)
    return (a[0][b[0]], a[1][b[1]])
def is_fpf(g):
    return not (np.any(g[0] == idp) or np.any(g[1] == idl))
tried = {}
t0 = time.time(); hits = []
budget = float(sys.argv[3]) if len(sys.argv) > 3 else 80
g = (idp, idl)
steps = 0
while time.time() - t0 < budget:
    # random walk element
    x = (idp, idl)
    for _ in range(40):
        x = mul(rng.choice(gens), x)
    if not is_fpf(x): continue
    # order and freeness of the cyclic group
    pw = [x]; y = x; ok = True
    while True:
        y = mul(x, y)
        if np.array_equal(y[0], idp):
            break
        if not is_fpf(y) or len(pw) > 80: ok = False; break
        pw.append(y)
    if not ok: continue
    k = len(pw) + 1
    if k in tried: tried[k] += 1; continue
    nq, E = orbit_quotient(hx, [(idp, idl)] + pw)
    # quotient diameter by BFS (pure python)
    adj = [[] for _ in range(nq)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    diam = 0; conn = True
    for s in range(nq):
        dist = [-1] * nq; dist[s] = 0; dq = [s]; h = 0
        while h < len(dq):
            u = dq[h]; h += 1
            for w in adj[u]:
                if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
        if len(dq) < nq: conn = False; break
        diam = max(diam, dist[dq[-1]])
    maxdeg = max(len(a) for a in adj)
    print(f'free cyclic order {k}: quotient vertices {nq} (2N/k={2*N//k}), simple max degree {maxdeg}, connected {conn}, diameter {diam if conn else "inf"}', flush=True)
    tried[k] = 1
    if conn and diam <= 5:
        hits.append((k, nq, diam))
        pickle.dump((k, [ (p.astype(np.int32), l.astype(np.int32)) for p, l in [(idp, idl)] + pw ]), open(f'hit_q{q}_k{k}_n{nq}.pkl', 'wb'))
print('done, hits', hits, 'orders tried', tried, flush=True)
