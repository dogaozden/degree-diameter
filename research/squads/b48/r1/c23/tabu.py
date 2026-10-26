# Tabu search over voltage assignments of pg23.txt (PG(2,3) incidence graph), scored by `lift ... eval` in batches.
# Tree edges (BFS from base vertex 0) fixed to identity (index 0); cotree edges (27) are free.
import sys, subprocess, random, time, os
T = '/home/user/degree-diameter/research/squads/b48/tools'
base_file, group, N, secs, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
out = sys.argv[6]
random.seed(seed)
lines = open(base_file).read().split('\n')
b, m = map(int, lines[0].split())
E = [tuple(map(int, lines[1 + i].split()[:2])) for i in range(m)]
# BFS spanning tree
adj = {v: [] for v in range(b)}
for i, (u, v) in enumerate(E):
    adj[u].append((v, i)); adj[v].append((u, i))
seen = {0}; q = [0]; intree = set()
while q:
    x = q.pop(0)
    for y, i in adj[x]:
        if y not in seen: seen.add(y); intree.add(i); q.append(y)
free = [i for i in range(m) if i not in intree]
def cost_batch(states):
    inp = []
    for s in states:
        v = [0] * m
        for k, i in enumerate(free): v[i] = s[k]
        inp.append(' '.join(map(str, v)))
    p = subprocess.run([f'{T}/lift', base_file, group, '4', '8', 'eval'], input='\n'.join(inp) + '\n',
                       capture_output=True, text=True, env=dict(os.environ, THREADS='1', QUIET='1'))
    res = []
    for ln in p.stdout.split('\n'):
        if ln.strip() == '': continue
        res.append(10**9 if ln.strip() == 'invalid' else int(ln))
    assert len(res) == len(states), (len(res), len(states), p.stderr[:300])
    return res
s = [random.randrange(N) for _ in free]
c = cost_batch([s])[0]
best, bests = c, list(s)
tabu = {}  # (coord, value) -> iteration until which setting value is forbidden
t0 = time.time(); it = 0
print('start', c, flush=True)
while time.time() - t0 < secs and best > 0:
    it += 1
    nb = []; meta = []
    for k in range(len(free)):
        for v in range(N):
            if v == s[k]: continue
            t = list(s); t[k] = v; nb.append(t); meta.append((k, v))
    costs = cost_batch(nb)
    order = sorted(range(len(nb)), key=lambda j: costs[j])
    pick = None
    for j in order:
        k, v = meta[j]
        if tabu.get((k, v), -1) < it or costs[j] < best:
            pick = j; break
    if pick is None: pick = order[0]
    k, v = meta[pick]
    tabu[(k, s[k])] = it + 8 + random.randrange(10)  # forbid restoring the old value for a while
    s = nb[pick]; c = costs[pick]
    if c < best:
        best, bests = c, list(s)
        print(f'it={it} t={time.time()-t0:.0f}s best={best}', flush=True)
    if it % 20 == 0: print(f'it={it} t={time.time()-t0:.0f}s cur={c} best={best}', flush=True)
full = [0] * m
for k, i in enumerate(free): full[i] = bests[k]
open(out, 'w').write(' '.join(map(str, full)) + '\n')
print('RESULT tabu base=%s group=%s N=%d n=%d best=%d iters=%d time=%.0f' % (base_file, group, N, b*N, best, it, time.time()-t0), flush=True)
