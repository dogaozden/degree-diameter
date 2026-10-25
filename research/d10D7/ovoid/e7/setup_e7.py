"""Find 7 vectors in F_q^7 (hex coordinates) with Gram matrix = E7 Cartan matrix; roots = their W(E7)-orbit."""
import numpy as np, random, sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/d10D7/ovoid/e7')
from common11 import *
q = int(sys.argv[1]) if len(sys.argv) > 1 else 5
G = Geo(q)
# E7 Dynkin (Bourbaki): 1-3, 3-4, 4-5, 5-6, 6-7, 2-4
edges = [(1,3),(3,4),(4,5),(5,6),(6,7),(2,4)]
Cart = np.zeros((7,7), dtype=np.int64)
for i in range(7): Cart[i,i] = 2
for a,b in edges: Cart[a-1,b-1] = Cart[b-1,a-1] = -1
rng = random.Random(1)
def solve_affine(rows, rhs):
    # all x in F_q^7 with rows @ x = rhs (mod q); return list of basis vectors and particular solution via brute Gauss
    M = [[int(x) for x in r] + [int(b)] for r, b in zip(rows, rhs)]
    n = 7; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] % q), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        iv = pow(M[r][c], q-2, q); M[r] = [(x*iv) % q for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % q:
                f = M[i][c]; M[i] = [(x - f*y) % q for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    part = [0]*n
    for i, c in enumerate(piv): part[c] = M[i][n]
    basis = []
    for f in free:
        v = [0]*n; v[f] = 1
        for i, c in enumerate(piv): v[c] = (-M[i][f]) % q
        basis.append(v)
    return np.array(part), [np.array(b) for b in basis]
def find_simple(seed):
    rng = random.Random(seed)
    a = []
    for i in range(7):
        rows = []; rhs = []
        for j in range(i):
            rows.append([int(x) for x in (A7 @ a[j]) % q]); rhs.append(int(Cart[j, i]) % q)
        if rows:
            part, basis = solve_affine(rows, rhs)
        else:
            part, basis = np.zeros(7, dtype=np.int64), [np.eye(7, dtype=np.int64)[k] for k in range(7)]
        for _ in range(20000):
            coef = [rng.randrange(q) for _ in basis]
            v = (part + sum(c*b for c, b in zip(coef, basis))) % q
            if (v @ A7 @ v) % q == 2 % q:   # B(v,v) = 2 Q(v) = 2
                a.append(v); break
        else:
            return None
    return np.array(a)
for s in range(1, 200):
    a = find_simple(s)
    if a is not None: break
Gram = (a @ A7 @ a.T) % q
print('Gram ok:', np.array_equal(Gram, Cart % q))
print(a.tolist())
# roots: orbit of simple roots under simple reflections r_i(x) = x - B(x,a_i) a_i  (mod q)
def refl(x, v):
    return (x - ((x @ A7 @ v) % q) * v) % q
roots = set(tuple(int(x) for x in v) for v in a) | set(tuple(int(x) for x in (-v) % q) for v in a)
frontier = list(roots)
while frontier:
    new = []
    for r in frontier:
        for v in a:
            w = tuple(refl(np.array(r), v).tolist())
            if w not in roots: roots.add(w); new.append(w)
    frontier = new
print('number of roots mod q:', len(roots))
pickle.dump({'simple': a, 'roots': sorted(roots), 'q': q}, open('/home/user/degree-diameter/research/d10D7/ovoid/e7/e7_q%d.pkl' % q, 'wb'))
