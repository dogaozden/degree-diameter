"""SA over hole patterns z in F_11^122 (cov-0 search).  Objective: omega(G[A_z]) + 0.02*|A_z|.
usage: holes_sa.py SEED ITERS START {c25|random} OUTPREFIX"""
import sys, os, random, time, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from holes import *
def read_offsets(path):
    V = []
    for line in open(path):
        t = line.split()
        if not t or t[0].startswith('#'): continue
        a, b, c, e, f = [int(z) for z in t[:5]]
        V.append((((e + 2 * a) % Q), b % Q, c % Q, f % Q))
    return sorted(set(V))
seed, iters, start, outp = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
rng = random.Random(seed)
def evaluate(z):
    A = A_of_pattern(z)
    if len(A) == 0: return 0, 0, []
    cl = max_clique(adjacent_matrix(A))
    return len(cl), len(A), [int(A[i]) for i in cl]
if start == 'c25':
    K0 = read_offsets('/home/user/degree-diameter/research/d13D7/sets/R320_offsets29_u1-0-0-9-0.txt')
    R4 = [(0,0,0,0), (4,5,8,1), (4,6,9,0), (4,9,10,7)]
    C25 = [v for v in K0 if v not in R4]
    z = []
    for n in D:
        vals = {int(sum(n[k]*v[k] for k in range(4)) % Q) for v in C25}
        free = [t for t in range(Q) if t not in vals]
        z.append(rng.choice(free))
else:
    z = [rng.randrange(Q) for _ in range(len(D))]
z = np.array(z)
w, na, cl = evaluate(z)
cur = w + 0.02 * na
best = (w, na); bestz = z.copy(); bestcl = cl
print('start omega', w, '|A|', na, flush=True)
T0, T1 = 0.6, 0.02
t0 = time.time()
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
    n = rng.randrange(len(D))
    old = z[n]
    new = rng.choice([t for t in range(Q) if t != old])
    z[n] = new
    w2, na2, cl2 = evaluate(z)
    f2 = w2 + 0.02 * na2
    if f2 >= cur or rng.random() < math.exp((f2 - cur) / T):
        cur = f2
        if (w2, na2) > best:
            best = (w2, na2); bestz = z.copy(); bestcl = cl2
            print(f'it {it} T {T:.3f} new best omega {w2} |A| {na2} t={time.time()-t0:.0f}s', flush=True)
            if w2 >= 26:
                np.save(outp + '_z26.npy', bestz)
    else:
        z[n] = old
np.save(outp + '_bestz.npy', bestz)
with open(outp + '_bestclique.txt', 'w') as f:
    f.write(f'# omega {best[0]} |A| {best[1]}\n')
    for i in bestcl:
        v = V4[i]
        f.write(f'0 {v[1]} {v[2]} {v[0]} {v[3]}\n')
print('done best', best, 'time', round(time.time()-t0), 's', flush=True)
