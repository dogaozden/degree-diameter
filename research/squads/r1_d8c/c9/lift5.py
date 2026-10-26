"""Step 3-4 of card c9: matching sigma with e(sigma^-1(l)) = -c(l) (mod 8), sigma(p) not incident to p,
then write the Z_8 lift file for glift (one matching, zero hexagon voltages, Delta = 7)."""
import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

q = 5; M = 8; K = 7
HERE = '/home/user/degree-diameter/research/squads/r1_d8c/c9/'
N, LP, PL, coord = load(q)
z = np.load(HERE + 'colours_q5.npz')
col, e = z['col'], z['e']
c_val = col + 1                      # line colour as Z_8 value in 1..7
inc = [set(LP[l].tolist()) for l in range(N)]
random.seed(1)

def match(P, L):
    """perfect matching P -> L avoiding incidences (Kuhn augmenting paths)."""
    adj = {p: [l for l in L if p not in inc[l]] for p in P}
    mate_l = {}
    def try_p(p, seen):
        for l in adj[p]:
            if l in seen: continue
            seen.add(l)
            if l not in mate_l or try_p(mate_l[l], seen):
                mate_l[l] = p
                return True
        return False
    for p in P:
        if not try_p(p, set()):
            raise RuntimeError('no matching')
    return {p: l for l, p in mate_l.items()}

sigma = {}
for v in range(1, M):
    P = [p for p in range(N) if e[p] == v]
    L = [l for l in range(N) if c_val[l] == (-v) % M]
    assert len(P) == len(L), (v, len(P), len(L))
    sigma.update(match(P, L))
assert len(sigma) == N and len(set(sigma.values())) == N
# matching edges: point p -> line sigma(p) with voltage e(p)
rows = []
for p in range(N):
    for l in PL[p]:
        rows.append((p, N + int(l), 0))
for p in range(N):
    rows.append((p, N + sigma[p], int(e[p]) % M))
out = HERE + 'lift_q5_m8.txt'
with open(out, 'w') as f:
    f.write(f'Z {M}\n{2*N}\n')
    f.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    for r in rows:
        f.write('%d %d %d\n' % r)
print('wrote', out, 'edges', len(rows))
