"""Random-pool sampling: pool of random flags; sample pairwise-opposite triples and quadruples; mismatch statistics
and zeros. Usage: python3 pool_sample.py POOL NQUAD SEED"""
import sys, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r3/c1')
from lib import *
from collections import Counter

POOL, NQ, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time()
rng = np.random.default_rng(SEED)
flags = []
for _ in range(POOL):
    p = int(rng.integers(N)); l = int(H.PL[p, rng.integers(H.q + 1)])
    flags.append((p, l))
fds = [FD(p, l) for p, l in flags]
n = len(fds)
adj = [0] * n
for i in range(n):
    for j in range(i + 1, n):
        if opp(fds[i], fds[j]):
            adj[i] |= 1 << j; adj[j] |= 1 << i
print('pool', n, 'opp density', round(sum(bin(a).count('1') for a in adj) / (n * (n - 1)), 3), 'time', round(time.time() - t0, 1), flush=True)
# triples
tr = []
for i in range(n):
    for j in range(i + 1, n):
        if (adj[i] >> j) & 1:
            c = adj[i] & adj[j] & ~((1 << (j + 1)) - 1)
            while c:
                k = (c & -c).bit_length() - 1; c &= c - 1
                tr.append((i, j, k))
print('pool triples (pairwise opposite)', len(tr), flush=True)
samp = [tr[i] for i in rng.choice(len(tr), size=min(20000, len(tr)), replace=False)]
mt = [mismatch([fds[i] for i in t]) for t in samp]
print('triple mismatch: zero fraction', round(sum(m == 0 for m in mt) / len(mt), 4), 'distribution head', sorted(Counter(mt).items())[:10], flush=True)
# quadruples by random rejection
quads = []
seen = set()
tries = 0
while len(quads) < NQ and tries < 40 * NQ:
    tries += 1
    S = tuple(sorted(rng.choice(n, size=4, replace=False).tolist()))
    if S in seen: continue
    seen.add(S)
    a, b, c, d = S
    if (adj[a] >> b) & 1 and (adj[a] >> c) & 1 and (adj[a] >> d) & 1 and (adj[b] >> c) & 1 and (adj[b] >> d) & 1 and (adj[c] >> d) & 1:
        quads.append(S)
print('quads sampled', len(quads), 'tries', tries, flush=True)
mq = [mismatch([fds[i] for i in S]) for S in quads]
cq = Counter(mq)
print('quad mismatch: zeros', cq.get(0, 0), 'min', min(mq) if mq else None, 'lowest', sorted(cq.items())[:12], flush=True)
zeros = [quads[i] for i, m in enumerate(mq) if m == 0]
out = {'pool_flags': flags, 'zero_quads': [[list(flags[i]) for i in S] for S in zeros[:50]],
       'n_zero_quads': len(zeros), 'quad_min': min(mq) if mq else None, 'time': round(time.time() - t0, 1)}
json.dump(out, open('/home/user/degree-diameter/research/squads/d10D7-r3/c1/pool_sample_%d_%d.json' % (POOL, SEED), 'w'))
print('time', round(time.time() - t0, 1), flush=True)
