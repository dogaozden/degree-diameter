# Twin construction without matching: x (new A) adjacent to N(a*), y (new B) adjacent to N(b*).
# Each b in N(a*) loses one edge to some A-vertex a_b != a*; each a in N(b*) loses one edge to some B-vertex b'_a != b*.
# Removed edges are chosen at random (seeded); vertices x=nA, y=2nA+1 in the new numbering.
import sys, random
from graph import load
path, out, astar, bstar, seed, mode = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
rnd = random.Random(seed)
n, adj, E = load(path); nA = n // 2
Bstar = nA + bstar
NAs = list(adj[astar]); NBs = list(adj[Bstar])
removed = set()
used_ends = set()
def key(u, v): return (min(u, v), max(u, v))
for b in NAs:                       # each b in N(a*): drop one edge to some a != a* (and not b* etc.)
    cands = [a for a in adj[b] if a != astar and key(a, b) not in removed]
    if mode == 'nb_b': cands = [a for a in cands if a in NBs]  # prefer partners in N(b*) (free slot reused by y)
    a = rnd.choice(cands); removed.add(key(a, b))
for a in NBs:                       # each a in N(b*): drop one edge to some b != b*
    cands = [b for b in adj[a] if b != Bstar and key(a, b) not in removed]
    b = rnd.choice(cands); removed.add(key(a, b))
x = nA; y = 2 * nA + 1
newE = [(u, v + 1) for u, v in E if key(u, v) not in removed]
newE += [(x, b + 1) for b in NAs] + [(a, y) for a in NBs]
with open(out, 'w') as f:
    f.write(f'{2*nA+2}\n'); f.writelines(f'{u} {v}\n' for u, v in newE)
print('wrote', out, 'removed', len(removed), 'edges', len(newE), 'n', 2 * nA + 2, 'a*~b*', Bstar in adj[astar], flush=True)
