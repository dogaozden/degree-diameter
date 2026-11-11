"""Write the edge list of a bi-coset graph (bicoset.py) for apsp.c.  usage: python3 build_edges.py OUT VA VB x0 x1 x2 x3
Vertices: A-cosets 0..N-1, B-cosets N..2N-1 (N = 16380).  Edges Ag ~ B(x^-1 a g), a in A (16 per vertex)."""
import sys
from collections import deque
import bicoset as bc

out = sys.argv[1]
VA = [int(v) for v in sys.argv[2].split(',')]
VB = [int(v) for v in sys.argv[3].split(',')]
x = tuple(int(v) for v in sys.argv[4].split(','))
A = [(1, t, 0, 1) for t in bc.span(VA)]
B = [(1, t, 0, 1) for t in bc.span(VB)]
xi = bc.minv(x)
keyA = lambda g: min(bc.mmul(a, g) for a in A)
keyB = lambda g: min(bc.mmul(b, g) for b in B)
ids = {}
def vid(node):
    if node not in ids:
        ids[node] = len(ids)
    return ids[node]
# enumerate all vertices by BFS from the identity A-coset (graph is connected, checked by bicoset.run)
start = ('A', keyA((1, 0, 0, 1)))
seen = {start}
dq = deque([start])
edges = []
rep_of = {start: (1, 0, 0, 1)}
def nbrs(node):
    side, g = node
    if side == 'A':
        return [('B', keyB(bc.mmul(bc.mmul(xi, a), g))) for a in A]
    return [('A', keyA(bc.mmul(bc.mmul(x, b), g))) for b in B]
pairs = set()
while dq:
    u = dq.popleft()
    for w in nbrs(u):
        if u[0] == 'A':
            pairs.add((u, w))
        else:
            pairs.add((w, u))
        if w not in seen:
            seen.add(w); dq.append(w)
Aids = {}; Bids = {}
for u, w in pairs:
    Aids.setdefault(u, len(Aids)); Bids.setdefault(w, len(Bids))
N = len(Aids)
assert len(Bids) == N and len(pairs) == 16 * N, (len(Aids), len(Bids), len(pairs))
with open(out, 'w') as f:
    f.write(f'{2 * N}\n')
    for u, w in pairs:
        f.write(f'{Aids[u]} {N + Bids[w]}\n')
print('vertices', 2 * N, 'edges', len(pairs))
