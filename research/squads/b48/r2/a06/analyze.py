# a06 analysis: read a lift solution (dipole4 base, 2 vertices, 4 edges), BFS the Haar graph, list uncovered
# elements per side, group them by quotient coset (meta / abc structure), and count the non-backtracking walks
# of length <= 7 that land in each coset (a counting view of the floor).
import sys, struct, collections
import numpy as np
from itertools import product

def load_bin(path):
    with open(path, 'rb') as f:
        N = struct.unpack('<i', f.read(4))[0]
        T = np.frombuffer(f.read(N * N * 2), dtype=np.uint16).reshape(N, N).astype(np.int64)
    return N, T

def read_sol(path):
    volt = []; meta = {}
    for line in open(path):
        if line.startswith('e '):
            p = line.split(); volt.append(int(p[3]))
        elif line.startswith('group'):
            meta['group'] = line.split()[1]
    return volt, meta

def haar_adj(N, T, volt):
    # A vertex x -> x ; B vertex y -> N + y ; edge (A,x) ~ (B, x*g)
    adj = [[] for _ in range(2 * N)]
    for g in volt:
        for x in range(N):
            y = int(T[x, g])
            adj[x].append(N + y); adj[N + y].append(x)
    return adj

def bfs(adj, s):
    d = [-1] * len(adj); d[s] = 0; q = collections.deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if d[w] < 0:
                d[w] = d[u] + 1; q.append(w)
    return d

def walk_cosets(volt, quot_of, k_mod):
    # non-backtracking walks from A-vertex e of length 1,3,5,7 (alternating A->B->A...), endpoint in B;
    # image in the quotient: product of s_i (A->B) and s_i^{-1} (B->A). Returns the count per quotient class.
    # quot_of: function from group index to quotient label; quotient abelian with additive labels mod k_mod.
    cnt = collections.Counter()
    m = len(volt)
    def rec(last, depth, acc, length):
        # at a B-vertex after an odd number of steps; record it
        pass
    # enumerate index sequences explicitly
    total = {}
    stack = [(None, 0, 0, 0)]  # (last edge index, step count, label sum, length)
    for L in range(1, 8, 2):
        pass
    cur = [(None, 0)]  # (last index, label)
    for step in range(1, 8):
        new = []
        for last, lab in cur:
            for i in range(m):
                if last is not None and i == last:
                    continue
                s = quot_of(volt[i])
                # step is odd: A->B adds +s ; step even: B->A adds -s
                nl = (lab + s) % k_mod if step % 2 == 1 else (lab - s) % k_mod
                new.append((i, nl))
        cur = new
        if step % 2 == 1:
            for _, lab in cur:
                cnt[lab] += 1
    return cnt

if __name__ == '__main__':
    tab, sol, mode = sys.argv[1], sys.argv[2], sys.argv[3]   # mode: 'M:K' (M-part size, quotient order)
    N, T = load_bin(tab)
    volt, meta = read_sol(sol)
    adj = haar_adj(N, T, volt)
    dA = bfs(adj, 0); dB = bfs(adj, N)
    unA = [x for x in range(N) if dA[N + x] > 8]   # B-elements far from A0
    unB = [y for y in range(N) if dB[y] > 8]        # A-elements far from B0
    print('volt', volt, 'N', N, 'n', 2 * N)
    print('cost', len(unA) + len(unB), 'uncovered B (from A0):', len(unA), 'uncovered A (from B0):', len(unB))
    print('dist of uncovered B:', collections.Counter(dA[N + x] for x in unA))
    print('dist of uncovered A:', collections.Counter(dB[x] for x in unB))
    M, K = [int(v) for v in mode.split(':')]
    print('volt-quotients', [v // M for v in volt])
    print('M-part', M, 'quotient', K)
    for name, lst in (('B-side', unA), ('A-side', unB)):
        print(name, [(x // M, x % M) for x in lst])
