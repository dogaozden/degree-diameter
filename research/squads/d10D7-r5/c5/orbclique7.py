# c5: orbit graph of <T> on Q(6,7): self-compatible orbits, compatibility, max weight clique (exact, small).
import numpy as np, sys, pickle, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from h7 import *
q, N, lines, coords = load_hex(HEX7)
orbits = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r5/c5/torus7_orbits.pkl', 'rb'))
J = np.zeros((7, 7), dtype=np.int64)
for a, b in [(0, 4), (1, 5), (2, 6)]: J[a, b] = 1; J[b, a] = 1
J[3, 3] = -2
Bfull = lambda Xa, Yb: (Xa @ J @ Yb.T) % q
self_ok = []
for k, o in enumerate(orbits):
    X = coords[o]
    Bm = Bfull(X, X)
    np.fill_diagonal(Bm, 1)
    if (Bm != 0).all(): self_ok.append(k)
print('self-compatible orbits:', len(self_ok), 'sizes', sorted(set(len(orbits[k]) for k in self_ok)))
reps = {k: orbits[k][0] for k in self_ok}
M = len(self_ok)
A = np.zeros((M, M), dtype=bool)
t0 = time.time()
for i, k in enumerate(self_ok):
    x = coords[reps[k]]
    for j, l in enumerate(self_ok):
        if j <= i: continue
        ok = (Bfull(x[None, :], coords[orbits[l]])[0] != 0).all()
        A[i, j] = A[j, i] = ok
print('compat graph built', round(time.time() - t0, 1), 's; edges', int(A.sum() // 2), 'of', M * (M - 1) // 2)
w = np.array([len(orbits[k]) for k in self_ok])
# greedy + simple branch and bound for max weight clique
best = [0, []]
def bb(cand, cur, cw):
    # cand: list of indices (into self_ok) compatible with all of cur
    if cw > best[0]: best[0] = cw; best[1] = list(cur)
    if not cand: return
    # upper bound: current + sum of weights of cand
    if cw + sum(w[c] for c in cand) <= best[0]: return
    for idx_, c in enumerate(cand):
        rest = [d for d in cand[idx_ + 1:] if A[c, d]]
        if cw + w[c] + sum(w[d] for d in rest) <= best[0]: continue
        bb(rest, cur + [c], cw + w[c])
        if time.time() - t0 > 600: return
bb(list(range(M)), [], 0)
print('max weight clique found:', best[0], 'orbits', len(best[1]), 'time', round(time.time() - t0, 1))
pickle.dump([orbits[self_ok[c]] for c in best[1]], open('/home/user/degree-diameter/research/squads/d10D7-r5/c5/torus7_best_clique.pkl', 'wb'))
