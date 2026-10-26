"""Card c5: fixed freed set R (random greedy partial ovoid of W(5)), simulated annealing over bijections M: points -> lines.
Violation V(M) = E1 violations + sum_{x in R} (E2 uncovered points + E3 unblocked lines), computed from the
criteria of repair.exact_conditions.  usage: sa_fixedR.py K SEED ITERS [T0]
Prints JSON {"R":..,"M":..} to stdout only when V == 0 and exact_conditions / brute_bad agree."""
import sys, json, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W
from repair import exact_conditions, brute_bad

K, seed, ITERS = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
T0 = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
rng = random.Random(seed); nrng = np.random.default_rng(seed)
G = W(5); n = 156
I = G.I.astype(np.int32)           # points x lines
IT = I.T.copy()
con = G.con                         # lines x lines (bool, irreflexive)
col = G.col
order = list(range(n)); rng.shuffle(order)
R = []
for p in order:
    if len(R) >= K: break
    if all(not col[p, x] for x in R): R.append(p)
R = np.array(R)
notR = np.ones(n, bool); notR[R] = False
Nx = [np.nonzero(col[x] & notR)[0] for x in R]    # Gamma2(x) minus R

def V(M):
    indR = np.zeros(n, np.int32); indR[M[R]] = 1
    v1 = int(np.count_nonzero(I @ indR == 6))      # points with all 6 lines in M(R)
    v2 = v3 = 0
    for i, x in enumerate(R):
        ind = np.zeros(n, np.int32); ind[M[Nx[i]]] = 1
        v2 += int(n - np.count_nonzero((I @ ind) > 0))          # uncovered points (E2)
        Tm = (con[M[x]][M] & notR).astype(np.int32)              # a not in R, M(a) concurrent with M(x)
        v3 += int(n - np.count_nonzero((IT @ Tm) > 0))           # unblocked lines (E3)
    return v1 + v2 + v3

M = np.arange(n); nrng.shuffle(M)
cur = V(M); best = cur; bestM = M.copy()
t0 = time.time()
for it in range(ITERS):
    if best == 0: break
    T = T0 * (1 - it / ITERS) + 0.02
    a, b = rng.randrange(n), rng.randrange(n)
    if a == b: continue
    M[a], M[b] = M[b], M[a]
    new = V(M)
    if new <= cur or rng.random() < np.exp(-(new - cur) / T):
        cur = new
        if cur < best:
            best = cur; bestM = M.copy()
    else:
        M[a], M[b] = M[b], M[a]
    if it % 20000 == 0:
        print('it', it, 'cur', cur, 'best', best, 'time %.0f' % (time.time() - t0), file=sys.stderr, flush=True)
print('K', len(R), 'best V', best, 'time %.0f' % (time.time() - t0), file=sys.stderr, flush=True)
Rl = [int(x) for x in R]; Ml = [int(x) for x in bestM]
good, fails = exact_conditions(G, 'H', 'H', Ml, Rl)
bad = brute_bad(G, 'H', 'H', bestM, Rl)
print('exact_conditions', good, 'brute_bad', bad, file=sys.stderr)
if good and bad == 0:
    print(json.dumps({'R': Rl, 'M': Ml}))
