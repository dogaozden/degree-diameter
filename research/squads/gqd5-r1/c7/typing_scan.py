import itertools, sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
n, conn = 5, (1, 2)
arcs = [(j, (j + k) % n) for j in range(n) for k in conn]
a, b, c = 26, 21, 0   # H->D: ovoid of Q(4,5); D->H: partial spread of Q(4,5) (partial ovoid of W(5), Tallini 21); H->H, D->D: 0
res = []
for types in itertools.product('HD', repeat=n):
    def cap(u, v):
        if types[u] == 'H' and types[v] == 'D': return a
        if types[u] == 'D' and types[v] == 'H': return b
        return c
    out = [0]*n; inn = [0]*n
    for (u, v) in arcs:
        w = cap(u, v); out[u] += w; inn[v] += w
    res.append((min(out) + min(inn), min(inn), min(out), ''.join(types), out, inn))
res.sort(key=lambda x: -x[0])
for r_ in res[:8]:
    print(r_)
