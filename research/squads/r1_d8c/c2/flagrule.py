"""c2: flags-as-vertices design for odd q (q=3 screen).
Per level i in Z5: block of F + 4N vertices: flags F = N(q+1) (local 0..F-1), copies X_t(e) = F + t*N + e
for t in {0:P1,1:P2,2:L1,3:L2}, e = point (t<2) or line (t>=2).
Edges (all flag-copy, so bipartite with flags vs copies):
  star:  flag (p,L) at level i ~ copy t at level i+s_t, element = p (t<2) or L (t>=2)  [s_0 = 0]
  match: a 4-edge-colouring kappa of I(H) (colour classes = perfect matchings); for j=1,2:
         flag of colour k ~ copy sigma_j[k] at level i+t_j, element p or L (a bijection flags -> copies).
Each copy gets 4 star edges + 2 matching edges, each flag 4 + 2: max degree q+3 = 6 when no duplicates.
Usage: python3 flagrule.py SEED_COLOURING s1 s2 s3 t1 t2 sig1 sig2 OUTFILE   (sig = 4 digits, a permutation)
"""
import sys, random
sys.setrecursionlimit(10000)
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import numpy as np
from hexlib import load

q = 3
N, LP, PL, coord = load(q)
L = N
flag_p = LP.reshape(-1).astype(int)
flag_l = np.repeat(np.arange(L), q + 1).astype(int)
F = len(flag_p)
B = F + 4 * N
NL = 5


def colouring(seed):
    """Proper 4-edge-colouring of the 4-regular bipartite incidence graph: 4 perfect matchings found by Kuhn."""
    rng = random.Random(seed)
    col = np.full(F, -1)
    for k in range(q + 1):
        rem = np.nonzero(col < 0)[0]
        adj = [[] for _ in range(N)]
        for f in rem:
            adj[flag_p[f]].append(f)
        for a in adj:
            rng.shuffle(a)
        matchL = [-1] * N
        def aug(p, seen):
            for f in adj[p]:
                l = flag_l[f]
                if l in seen:
                    continue
                seen.add(l)
                if matchL[l] == -1 or aug(flag_p[matchL[l]], seen):
                    matchL[l] = f
                    return True
            return False
        order = list(range(N)); rng.shuffle(order)
        for p in order:
            ok = aug(p, set())
            assert ok, 'no perfect matching'
        for l in range(N):
            col[matchL[l]] = k
    assert (np.bincount(col) == N).all()
    return col


def build(cseed, s, t, sig, out):
    col = colouring(cseed)
    edges = set()
    def gid(i, loc):
        return (i % NL) * B + loc
    for i in range(NL):
        for f in range(F):
            p, l = flag_p[f], flag_l[f]
            u = gid(i, f)
            for tt in range(4):
                e = p if tt < 2 else l
                edges.add((min(u, gid(i + s[tt], F + tt * N + e)), max(u, gid(i + s[tt], F + tt * N + e))))
            for j in range(2):
                T = sig[j][col[f]]
                e = p if T < 2 else l
                v = gid(i + t[j], F + T * N + e)
                edges.add((min(u, v), max(u, v)))
    E = sorted(edges)
    deg = np.zeros(NL * B, dtype=int)
    for a, b in E:
        deg[a] += 1; deg[b] += 1
    with open(out, 'w') as fh:
        fh.write(f'{NL * B}\n')
        fh.write('\n'.join(f'{a} {b}' for a, b in E))
        fh.write('\n')
    return len(E), int(deg.max()), int(deg.min())


if __name__ == '__main__':
    cseed = int(sys.argv[1])
    s = [0] + [int(x) for x in sys.argv[2:5]]
    t = [int(sys.argv[5]), int(sys.argv[6])]
    sig = [[int(c) for c in sys.argv[7]], [int(c) for c in sys.argv[8]]]
    out = sys.argv[9]
    print(build(cseed, s, t, sig, out))
