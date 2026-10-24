"""Profile unreached targets of a Z_M1 x Z_M2 lift (base file in liftdiam format) from a few sources:
classify each unreached lift vertex (y, g) by (H(q)-distance d(x,y), g) for source (x, 0)."""
import collections
import sys
import numpy as np
import gh


def load_base(path):
    with open(path) as fh:
        NB, M1, M2, E = map(int, fh.readline().split())
        adj = [[] for _ in range(NB)]
        for _ in range(E):
            u, v, a, b = map(int, fh.readline().split())
            adj[u].append((v, a % M1, b % M2))
            adj[v].append((u, (-a) % M1, (-b) % M2))
    return NB, M1, M2, adj


def bfs(NB, M1, M2, adj, src, D):
    M = M1 * M2
    dist = np.full(NB * M, 255, dtype=np.uint8)
    dist[src * M] = 0
    fr = [src * M]
    for lev in range(1, D + 1):
        nf = []
        for w in fr:
            v, g = divmod(w, M)
            g1, g2 = divmod(g, M2)
            for (u, a, b) in adj[v]:
                h = ((g1 + a) % M1) * M2 + (g2 + b) % M2
                z = u * M + h
                if dist[z] == 255:
                    dist[z] = lev
                    nf.append(z)
        fr = nf
    return dist


if __name__ == '__main__':
    path, q = sys.argv[1], int(sys.argv[2])
    srcs = [int(s) for s in sys.argv[3].split(',')]
    H = gh.load(q)
    Dm, _ = gh.distances(H)
    NB, M1, M2, adj = load_base(path)
    M = M1 * M2
    for s in srcs:
        dist = bfs(NB, M1, M2, adj, s, 8)
        cnt = collections.Counter()
        for z in np.nonzero(dist == 255)[0]:
            y, g = divmod(int(z), M)
            g1, g2 = divmod(g, M2)
            cnt[(int(Dm[s, y]), g1)] += 1
        print(f'source {s}: unreached {sum(cnt.values())}; by (d(x,y), Z_{M1}-part):', dict(sorted(cnt.items())))
