#!/usr/bin/env python3
"""lns.py GRAPH SOL OUT SECONDS SEED [KMIN KMAX SUBBUDGET]: exact large-neighbourhood search for a maximum-weight
independent set of a quotient graph (format: "n", then "w deg nbrs..."). Destroy: keep a random subset K of the current
set S (|K| in [KMIN, KMAX]). Repair: the vertices with no neighbour in K form the free region R; MWIS on R is solved
exactly by ./mwis_bb (time-limited, SUBBUDGET CPU seconds) with S minus K as the incumbent. Improvements are written to
OUT (quotient ids) at once. Prints one line per improvement and a summary."""
import sys, random, subprocess, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
gf, sf, of = sys.argv[1], sys.argv[2], sys.argv[3]
T = float(sys.argv[4]); seed = int(sys.argv[5])
kmin = int(sys.argv[6]) if len(sys.argv) > 6 else 4
kmax = int(sys.argv[7]) if len(sys.argv) > 7 else 10
sub_budget = float(sys.argv[8]) if len(sys.argv) > 8 else 5.0
rnd = random.Random(seed)
with open(gf) as f:
    n = int(f.readline())
    w = [0] * n
    adj = [set() for _ in range(n)]
    for i in range(n):
        a = list(map(int, f.readline().split()))
        w[i] = a[0]
        adj[i] = set(a[2:2 + a[1]])
S = set(int(x) for x in open(sf) if x.strip())
assert all(not (adj[v] & S) for v in S), 'start set not independent'
W = sum(w[v] for v in S)
print('start weight', W, 'size', len(S), flush=True)
tmpdir = os.path.join(HERE, 'lns_tmp_%d' % seed)
os.makedirs(tmpdir, exist_ok=True)
t0 = time.time(); it = 0; nimp = 0; nexact = 0; ntime = 0
while time.time() - t0 < T:
    it += 1
    k = rnd.randint(kmin, min(kmax, len(S)))
    K = set(rnd.sample(sorted(S), k))
    blocked = set(K)
    for v in K:
        blocked |= adj[v]
    R = [v for v in range(n) if v not in blocked]
    wK = sum(w[v] for v in K)
    init = [v for v in S if v not in K]          # all of them lie in R (S is independent)
    idx = {v: i for i, v in enumerate(R)}
    gp = os.path.join(tmpdir, 'sub.txt'); ip = os.path.join(tmpdir, 'init.txt'); op = os.path.join(tmpdir, 'out.txt')
    with open(gp, 'w') as g:
        g.write('%d\n' % len(R))
        for v in R:
            nb = [idx[u] for u in adj[v] if u in idx]
            g.write('%d %d %s\n' % (w[v], len(nb), ' '.join(map(str, nb))))
    with open(ip, 'w') as g:
        g.write('\n'.join(str(idx[v]) for v in init) + ('\n' if init else ''))
    out = subprocess.run([os.path.join(HERE, 'mwis_bb'), gp, ip, op, str(sub_budget)], capture_output=True, text=True)
    res = [l for l in out.stdout.split('\n') if l.startswith('RESULT')]
    if not res:
        print('subproblem failed', out.stderr[-300:], flush=True); break
    if 'status=COMPLETE' in res[0]:
        nexact += 1
    else:
        ntime += 1
    newR = [R[int(x)] for x in open(op) if x.strip()]
    newS = K | set(newR)
    neww = sum(w[v] for v in newS)
    assert not any(adj[v] & newS for v in newS), 'repair not independent'
    if neww > W:
        nimp += 1
        print('it %d |R|=%d k=%d improved %d -> %d (size %d) t=%.0f' % (it, len(R), k, W, neww, len(newS),
              time.time() - t0), flush=True)
        S, W = newS, neww
        with open(of, 'w') as g:
            g.write('\n'.join(map(str, sorted(S))) + '\n')
    if it % 50 == 0:
        print('it %d |R|=%d current %d exact %d timeouts %d t=%.0f' % (it, len(R), W, nexact, ntime, time.time() - t0),
              flush=True)
with open(of, 'w') as g:
    g.write('\n'.join(map(str, sorted(S))) + '\n')
print('END iters %d improvements %d exact %d timeouts %d best %d size %d' % (it, nimp, nexact, ntime, W, len(S)))
