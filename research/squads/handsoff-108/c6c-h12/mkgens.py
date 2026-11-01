# mkgens.py: generators of the candidate subgroups of order 12 in PGL(2,193) (c6c-h12)
q = 193
def mul(x, y):
    return ((x[0]*y[0]+x[1]*y[2]) % q, (x[0]*y[1]+x[1]*y[3]) % q, (x[2]*y[0]+x[3]*y[2]) % q, (x[2]*y[1]+x[3]*y[3]) % q)
def norm(x):
    for v in x:
        if v % q:
            inv = pow(v, q-2, q)
            return tuple((u*inv) % q for u in x)
    raise ValueError("zero matrix")
def closure(gens, cap=60):
    e = norm((1,0,0,1)); G = {e}; fr = [e]
    while fr:
        nf = []
        for g in fr:
            for h in gens:
                p = norm(mul(g, h))
                if p not in G:
                    G.add(p); nf.append(p)
                    if len(G) > cap: return G
        fr = nf
    return G
def is_scalar(x):
    return x[1] % q == 0 and x[2] % q == 0 and x[0] % q == x[3] % q
def order_pgl(x, cap=50):
    p = x; n = 1
    while not is_scalar(p):
        p = norm(mul(p, x)); n += 1
        if n > cap: return None
    return n
def is_prim(g):
    return all(pow(g, 192//p, q) != 1 for p in (2, 3))
g = next(x for x in range(2, q) if is_prim(x))
a6 = pow(g, 32, q)
sq = lambda d: pow(d % q, (q-1)//2, q) == 1
c_sq = next(c for c in range(2, q) if sq(c))
c_nsq = next(c for c in range(2, q) if not sq(c))
r = (a6, 0, 0, 1)
print("primitive root", g, "a6", a6, "order of r", order_pgl(r))
for name, c in [("D6sq", c_sq), ("D6nsq", c_nsq)]:
    s = (0, 1, c, 0)
    G = closure([r, s])
    print(name, "c", c, "order", len(G), "order of s", order_pgl(s), "det class square:", sq(-c), "r,s GEN:", r, s)
# A4 in PSL(2,193): V4 = {1,a,b,ab}, t of order 3 permuting a->b->ab
i = next(x for x in range(2, q) if (x*x) % q == q-1)
a = (0, 1, q-1, 0)
b = (i, 0, 0, (-i) % q)
ab = mul(a, b)
V4 = {norm((1,0,0,1)), norm(a), norm(b), norm(ab)}
print("V4 size", len(V4), "orders", order_pgl(a), order_pgl(b), order_pgl(ab))
# t a = b t  (linear in t)
def lin(t):
    return tuple((x - y) % q for x, y in zip(mul(t, a), mul(b, t)))
cols = [lin(e) for e in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]]
mat = [[cols[k][row] for k in range(4)] for row in range(4)]
def nullspace(mat):
    m = [row[:] for row in mat]; nr = len(m); nc = len(m[0]); piv = []; r0 = 0
    for c in range(nc):
        p = next((rr for rr in range(r0, nr) if m[rr][c] % q), None)
        if p is None: continue
        m[r0], m[p] = m[p], m[r0]
        inv = pow(m[r0][c], q-2, q); m[r0] = [(x*inv) % q for x in m[r0]]
        for rr in range(nr):
            if rr != r0 and m[rr][c] % q:
                f = m[rr][c]; m[rr] = [(x - f*y) % q for x, y in zip(m[rr], m[r0])]
        piv.append(c); r0 += 1
    free = [c for c in range(nc) if c not in piv]
    out = []
    for fcol in free:
        v = [0]*nc; v[fcol] = 1
        for idx, pc in enumerate(piv): v[pc] = (-m[idx][fcol]) % q
        out.append(v)
    return out
ns = nullspace(mat)
print("nullspace dim", len(ns))
found = None
for u in range(q):
    for w in range(q):
        if (u, w) == (0, 0): continue
        t = tuple((u*ns[0][k] + w*ns[1][k]) % q for k in range(4))
        if (t[0]*t[3] - t[1]*t[2]) % q == 0: continue
        if order_pgl(t) != 3: continue
        tbt = norm(mul(mul(t, b), (t[3], (-t[1]) % q, (-t[2]) % q, t[0])))
        if tbt in V4:
            found = t; break
    if found: break
print("A4 t", found)
G = closure([a, found], cap=100)
print("A4 closure order", len(G), "GEN", a, found)
