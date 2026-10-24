"""Generic lattice bound for voltage lifts (rigorous): for a base B with c independent cycles and abelian voltage
image, the most distinct endpoints (v, value) of walks of length <= D from a source come from the free abelian group
Z^c with the cycle voltages as a basis (gauge-fixed tree edges = 0).  Every vertex (v, a) of the lift by A = G/G'
must be reached, so |B| * |G^ab| <= min over sources of that count.  Usage: python3 liftbound.py BASE D"""
import sys
def read_base(path):
    L = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    k = int(L[0][0]); E = []
    for t in L[1:]:
        E.append((int(t[0]), int(t[1]), len(t) > 2 and t[2] == '='))
    return k, E
def bound(path, D):
    k, E = read_base(path)
    free = [i for i, e in enumerate(E) if not e[2]]
    c = len(free)
    adj = {u: [] for u in range(k)}
    for i, (w, b, fixed) in enumerate(E):
        vec = tuple(1 if (j == free.index(i) if i in free else False) else 0 for j in range(c))
        adj[w].append((b, vec, 1)); adj[b].append((w, vec, -1))
    counts = []
    for src in range(k):
        seen = {(src, (0,) * c)}; front = set(seen)
        for _ in range(D):
            nf = set()
            for (u, x) in front:
                for (v, vec, sg) in adj[u]:
                    y = tuple(a + sg * b for a, b in zip(x, vec))
                    if (v, y) not in seen:
                        seen.add((v, y)); nf.add((v, y))
            front = nf
        counts.append(len(seen))
    return k, c, min(counts)
if __name__ == '__main__':
    k, c, m = bound(sys.argv[1], int(sys.argv[2]))
    print(f'base {sys.argv[1]}: {k} vertices, {c} free voltages; min over sources of generic endpoints = {m}; '
          f'so |G^ab| <= {m // k}')
