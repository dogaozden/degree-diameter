# Coordinator's own build of the bipartite flag graph of PG(4,3): sides (W1<W3) and (W2<W4) in GF(3)^5,
# adjacent iff W1<W2<W3<W4. Subspaces are bitmasks over the 243 vectors. Writes an edge list for apsp.c.
import itertools, sys
q, n = 3, 5
vecs = list(itertools.product(range(q), repeat=n)); idx = {v: i for i, v in enumerate(vecs)}
def span(gens):
    s = {tuple([0]*n)}
    for g in gens:
        s = {tuple((a + c*b) % q for a, b in zip(x, g)) for x in s for c in range(q)}
    return sum(1 << idx[v] for v in s)
nz = [v for v in vecs if any(v)]
sub = {1: {span([v]) for v in nz}}
members = lambda m: [vecs[i] for i in range(len(vecs)) if m >> i & 1]
def basis(m):
    b, s = [], 1 << idx[tuple([0]*n)]
    for v in members(m):
        if not (s >> idx[v] & 1):
            b.append(v); s = span(b)
    return b
for d in (2, 3, 4):
    sub[d] = set()
    for m in sub[d-1]:
        bm = basis(m)
        for v in nz:
            if not (m >> idx[v] & 1):
                sub[d].add(span(bm + [v]))
print({d: len(sub[d]) for d in sub}, file=sys.stderr)
inc = lambda a, b: a & b == a
L = {d: sorted(sub[d]) for d in sub}
down = {d: {m: [x for x in L[d-1] if inc(x, m)] for m in L[d]} for d in (2, 3, 4)}
A, B, E = {}, {}, []
for w4 in L[4]:
    for w3 in down[4][w4]:
        for w2 in down[3][w3]:
            for w1 in down[2][w2]:
                a = A.setdefault((w1, w3), len(A)); b = B.setdefault((w2, w4), len(B)); E.append((a, b))
nA = 15730
assert len(A) == len(B) == nA, (len(A), len(B))
with open(sys.argv[1], 'w') as f:
    f.write(f'{2*nA}\n'); f.writelines(f'{a} {nA + b}\n' for a, b in E)
print('vertices', 2*nA, 'edges', len(E), file=sys.stderr)
