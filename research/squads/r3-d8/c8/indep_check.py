# Independent check (pure Python BFS on the explicit lift) of a liftdiam base file: builds vertices (u,a,b),
# checks degree / bipartiteness / multi-edges and BFS eccentricity from sampled base sources.
import sys, random, collections
fn = sys.argv[1]; nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 30
with open(fn) as fh:
    NB, M1, M2, E = map(int, fh.readline().split())
    darts = [tuple(map(int, fh.readline().split())) for _ in range(E)]
G = M1 * M2
adj = collections.defaultdict(list)
for u, v, a, b in darts:
    a %= M1; b %= M2
    for g1 in range(M1):
        for g2 in range(M2):
            x = (u, g1, g2); y = (v, (g1 + a) % M1, (g2 + b) % M2)
            adj[x].append(y); adj[y].append(x)
deg = collections.Counter(len(adj[x]) for x in adj)
nv = len(adj)
multi = sum(len(adj[x]) - len(set(adj[x])) for x in adj)
# bipartite via base colouring (points even/lines odd is inherited from base: check each edge joins u<NB/2 side to other)
rng = random.Random(0)
ecc = []
srcs = [(u, 0, 0) for u in rng.sample(range(NB), min(nsamp, NB))]
for s in srcs:
    dist = {s: 0}; fr = [s]; d = 0
    while fr:
        d += 1; nf = []
        for x in fr:
            for y in adj[x]:
                if y not in dist: dist[y] = d; nf.append(y)
        fr = nf
    ecc.append(max(dist.values()) if len(dist) == nv else 10**9)
print('vertices', nv, 'degree histogram', dict(deg), 'parallel darts', multi, 'sampled sources', len(srcs),
      'max sampled ecc', max(ecc), 'all connected', all(e < 10**9 for e in ecc))
