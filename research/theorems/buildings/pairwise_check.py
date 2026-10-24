"""Pairwise test of Theorem 2 (BUILDINGS.md) in PG(n,q): for a few source chambers C and EVERY chamber C', the BFS
distance from each part (odd/even members) of C to each part of C' must equal d_JK(delta(C, C')), with
delta(C, C') = the relative-position permutation w of the two complete flags (V_i), (V'_j):
    dim(V_i meet V'_j) = |{1..i} meet w({1..j})|,
and d_JK from the block BFS of weyl_dist.analyse (m_J(w) = level[J][w^-1 rho]).
usage: python3 pairwise_check.py n q SOURCES"""
import sys, runpy, io, contextlib, math, random
from collections import deque
n, q, nsrc = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
sys.argv = ['polar_flags.py', 'PG', str(n), str(q)]
with contextlib.redirect_stdout(io.StringIO()):
    G = runpy.run_path('polar_flags.py', run_name='__main__')
chambers, odd, even, adj = G['chambers'], G['odd'], G['even'], G['adj']
No = len(odd); top = n
from weyl_dist import analyse
C, I, cls, ncls, info, level = analyse('A', n)
# I[0] = nodes {0,2,..} (dims 1,3,..): a flag of odd dims is a residue of type I[1]; even dims: residue of type I[0]
def dim(mask): return int(round(math.log(bin(mask).count('1'), q)))
def relpos(c1, c2):
    full = n + 1
    V = [None] + list(c1) + [None]; W = [None] + list(c2) + [None]
    def d(i, j):
        if i == 0 or j == 0: return 0
        if i == full: return j
        if j == full: return i
        return dim(V[i] & W[j])
    w = [0] * (full + 1)
    for j in range(1, full + 1):
        for i in range(1, full + 1):
            if d(i, j) - d(i - 1, j) - d(i, j - 1) + d(i - 1, j - 1) == 1: w[j] = i
    return w[1:]          # w(j), j = 1..n+1
rho = list(range(n, -1, -1))   # epsilon-coordinates of rho for A_n
def lam_of_inverse(w):
    # w as a permutation of 1..n+1 (w(j)); lambda(u) for u = w^-1: u(rho)_i = rho_{u^-1(i)} = rho_{w(i)}
    u_rho = [rho[w[i] - 1] for i in range(n + 1)]
    return tuple(u_rho[i] - u_rho[i + 1] for i in range(n))
def predicted(J, K, w):
    m = level[J][lam_of_inverse(w)]
    Jm = J if m % 2 == 1 else 1 - J
    return m - (1 if Jm == K else 0)
def parts(c): return odd[tuple(c[i] for i in range(0, top, 2))], No + even[tuple(c[i] for i in range(1, top, 2))]
def bfs(s):
    dist = [-1] * len(adj); dist[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for x in adj[u]:
            if dist[x] < 0: dist[x] = dist[u] + 1; dq.append(x)
    return dist
random.seed(3)
checked = bad = 0
for c in random.sample(chambers, nsrc):
    o, e = parts(c)
    for src, J in ((o, 1), (e, 0)):
        dist = bfs(src)
        for c2 in chambers:
            w = relpos(c, c2)
            o2, e2 = parts(c2)
            for tgt, K in ((o2, 1), (e2, 0)):
                checked += 1
                if dist[tgt] != predicted(J, K, w): bad += 1
print(f"PG({n},{q}): {nsrc} source chambers x {len(chambers)} target chambers x 4 (source part, target part): "
      f"{checked} pairs checked, {bad} disagree with Theorem 2")
