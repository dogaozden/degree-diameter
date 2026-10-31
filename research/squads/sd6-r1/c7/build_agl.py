# Independent builder: Haar graph H(AGL(1,q), S), (g,A) ~ (s g, B), group law (u1,v1)(u2,v2) = (u1 u2, u1 v2 + v1).
# usage: build_agl.py q "u:v u:v ..." out.edges
import sys
q = int(sys.argv[1])
S = [tuple(map(int, t.split(':'))) for t in sys.argv[2].split()]
els = [(u, v) for u in range(1, q) for v in range(q)]
idx = {e: i for i, e in enumerate(els)}
N = len(els)
assert len(set(S)) == len(S) == 7
def mul(a, b):
    return ((a[0] * b[0]) % q, (a[0] * b[1] + a[1]) % q)
edges = []
for g in els:
    for s in S:
        edges.append((idx[g], N + idx[mul(s, g)]))
with open(sys.argv[3], 'w') as f:
    f.write('%d\n' % (2 * N))
    for a, b in edges:
        f.write('%d %d\n' % (a, b))
print('N=%d edges=%d' % (N, len(edges)))
