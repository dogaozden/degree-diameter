import sys, random, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/f65r1/c16')
import bases as B
from collections import deque

def bfs_ok(k, edges, D=5):
    adj = [[] for _ in range(k)]
    for x, y in edges:
        adj[x].append(y); adj[y].append(x)
    for s in range(k):
        dist = [-1]*k; dist[s] = 0; q = deque([s])
        while q:
            v = q.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v]+1; q.append(w)
        if min(dist) < 0 or max(dist) > D: return False
    return True

def write(name, k, edges, note):
    with open(f'bases/{name}.txt', 'w') as f:
        f.write(f'# {note}\nk {k}\n')
        for x, y in edges: f.write(f'e {x} {y}\n')
    print(name, k, len(edges), 'diam<=5' if bfs_ok(k, edges) else 'DIAM>5')

def haar(h, T):
    # white i (0..h-1), black h+j; edge i ~ h + ((i+t) mod h)
    return [(i, h + (i+t) % h) for i in range(h) for t in T]

def blowup(k_half, edges_named):
    # named bipartite base with white 0..h-1, black h..2h-1 (lift.c colours by BFS); blow each vertex to 2 copies, K_{2,2} per edge
    pass

def main():
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    # (a) cyclic Haar graphs H(Z_h, T), |T|=6, base diameter <=5
    for h in [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 23, 25, 27, 31]:
        for s in range(2):
            while True:
                T = rnd.sample(range(h), 6)
                e = haar(h, T)
                if bfs_ok(2*h, e): break
            write(f'haarZ{h}_{s}', 2*h, e, f'Haar H(Z{h},{sorted(T)})')
    # (a2) Z7 haar with difference-set-like T (Singer-ish): T={0,1,3,... } ; try a few fixed
    # (b) PG(2,5) incidence (girth 6) 31+31
    q = 5
    pts = [p for p in itertools.product(range(q), repeat=3) if p != (0,0,0) and next(x for x in p if x) == 1]
    pts = sorted(set(pts))
    e = [(i, 31 + j) for i, p in enumerate(pts) for j, l in enumerate(pts) if sum(a*b for a, b in zip(p, l)) % q == 0]
    write('pg25', 62, e, 'PG(2,5) incidence (6-regular, girth 6)')
    # (c) PG(2,4) incidence (5-regular) + random perfect matching of non-incident pairs
    # GF(4): elements 0,1,2(=w),3(=w+1); add = xor; mul table:
    mul = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
    P4 = []
    for p in itertools.product(range(4), repeat=3):
        if p == (0,0,0): continue
        f = next(x for x in p if x)
        if f == 1: P4.append(p)
    assert len(P4) == 21
    def dot(a, b):
        s = 0
        for x, y in zip(a, b): s ^= mul[x][y]
        return s
    inc = [[dot(p, l) == 0 for l in P4] for p in P4]
    for s in range(3):
        while True:
            perm = list(range(21)); rnd.shuffle(perm)
            if all(not inc[i][perm[i]] for i in range(21)): break
        e = [(i, 21+j) for i in range(21) for j in range(21) if inc[i][j]]
        e += [(i, 21+perm[i]) for i in range(21)]
        write(f'pg24m_{s}', 42, e, 'PG(2,4) incidence + random matching on non-incident pairs')
    # (d) K22 blow-ups of named cubic bipartite graphs
    for name in ['heawood', 'moebius_kantor', 'pappus', 'desargues']:
        k, f = B.NAMED[name]
        ed = f()
        # determine colours: BFS 2-colouring
        k2 = k
        adj = [[] for _ in range(k2)]
        for x, y in ed: adj[x].append(y); adj[y].append(x)
        col = [-1]*k2; col[0] = 0; st = [0]
        while st:
            v = st.pop()
            for w in adj[v]:
                if col[w] < 0: col[w] = 1-col[v]; st.append(w)
        W = [v for v in range(k2) if col[v] == 0]; K = [v for v in range(k2) if col[v] == 1]
        idx = {}
        for v in W: idx[(v, 0)] = len(idx); idx[(v, 1)] = len(idx)
        for v in K: idx[(v, 0)] = len(idx); idx[(v, 1)] = len(idx)
        be = []
        for x, y in ed:
            if col[x] == 1: x, y = y, x
            for i in range(2):
                for j in range(2):
                    be.append((idx[(x, i)], idx[(y, j)]))
        # re-index so that whites are first: whites are idx of W-vertices
        n = len(idx)
        white = sorted(idx[(v, i)] for v in W for i in range(2))
        wmap = {w: t for t, w in enumerate(white)}
        bl = sorted(set(range(n)) - set(white))
        bmap = {b: len(white)+t for t, b in enumerate(bl)}
        mp = {**wmap, **bmap}
        be2 = [(mp[x], mp[y]) for x, y in be]
        write(f'blow_{name}', n, be2, f'K22 blow-up of {name}')
    # (e) random 6-regular on h+h for comparison
    for h in [14, 17, 21, 24]:
        ed = B.perfect_matchings_regular(h, 6, rnd)
        write(f'rand_h{h}', 2*h, ed, f'random 6-regular {h}+{h}')

main()
