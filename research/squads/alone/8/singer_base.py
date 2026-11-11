# Z_121 quotient of the PG(4,3) flag graph under the Singer subgroup sigma = w^2 (w = root of a primitive quintic).
# Writes the base voltage graph "130 121 16" + "i j a" lines, where X-orbit i ~ Y-orbit j with voltage a.
import itertools, sys
q, n = 3, 5
vecs = list(itertools.product(range(q), repeat=n))          # coefficient tuples, c0..c4
def mulx(v, f):                                              # multiply by x modulo f (monic, f = [f0..f4])
    c = (0,) + v[:-1]; top = v[-1]
    return tuple((c[i] - top * f[i]) % q for i in range(n))
def order_of_x(f):
    v = (1, 0, 0, 0, 0); k = 0; seen = None
    for k in range(1, 243):
        v = mulx(v, f)
        if v == (1, 0, 0, 0, 0): return k
    return 10**9
f = next(f for f in itertools.product(range(q), repeat=n) if f[0] and order_of_x(f) == 242)
print('primitive f', f, file=sys.stderr)
w = {}                                                      # powers of w: w^k as vector tuples
v = (1, 0, 0, 0, 0)
for k in range(242): w[k] = v; v = mulx(v, f)
def mul_w(k):                                                # linear map v -> w^k * v as dict on vectors
    m = {}
    for x in vecs:
        # w^k * x : multiply polynomial x by w^k mod f
        acc = (0,) * n
        for i, c in enumerate(x):
            if c:
                # x = sum c_i * t_i (t_i = w^i), so w^k x = sum c_i * w^(k+i)
                acc = tuple((acc[j] + c * w[(k + i) % 242][j]) % q for j in range(n))
        m[x] = acc
    return m
sig = mul_w(2)                                              # sigma = w^2, order 121
def span(gens):
    s = {(0,) * n}
    for g in gens:
        s = {tuple((a + c * b) % q for a, b in zip(x, g)) for x in s for c in range(q)}
    return frozenset(s)
nz = [v for v in vecs if any(v)]
L = {1: {span([v]) for v in nz}}
for d in (2, 3, 4):
    L[d] = set()
    for m in L[d-1]:
        for v in nz:
            if v not in m:
                L[d].add(frozenset(m | {tuple((a + c * b) % q for a, b in zip(x, v)) for x in m for c in range(q)}))
print({d: len(L[d]) for d in L}, file=sys.stderr)
X = [(w1, w3) for w3 in L[3] for w1 in L[1] if w1 < w3]
Y = [(w2, w4) for w4 in L[4] for w2 in L[2] if w2 < w4]
print('X', len(X), 'Y', len(Y), file=sys.stderr)
def act(S, k):  # apply sigma^k to a subspace (frozenset of vectors)
    return frozenset(sig_k[k][x] for x in S)
sig_k = [{x: x for x in vecs}]
for k in range(1, 121): sig_k.append({x: sig[sig_k[-1][x]] for x in vecs})
def orbit_index(objs):
    ex = {}; reps = []
    for o in objs:
        if o in ex: continue
        idx = len(reps); reps.append(o)
        for k in range(121):
            ob = (act(o[0], k), act(o[1], k))
            ex[ob] = (idx, k)
    return reps, ex
Xr, Xex = orbit_index(X)
Yr, Yex = orbit_index(Y)
K = len(Xr); assert K == len(Yr) and K * 121 == len(X), (K, len(Yr), len(X))
print('orbits', K, file=sys.stderr)
E = set()
for i, (w1, w3) in enumerate(Xr):
    cnt = 0
    for w2 in L[2]:
        if not (w1 < w2 < w3): continue
        for w4 in L[4]:
            if w2 < w4 and w3 < w4:
                j, a = Yex[(w2, w4)]
                E.add((i, j, a)); cnt += 1
    assert cnt == 16, cnt
with open(sys.argv[1], 'w') as f:
    f.write(f'{K} 121 16\n')
    for i, j, a in sorted(E): f.write(f'{i} {j} {a}\n')
print('edges', len(E), file=sys.stderr)
