# Independent check of a metacyclic Haar graph solution, from the definition (no numpy, no bit tricks).
# Group Z_m x|_r Z_k: (a,j)(b,l) = (a + r^j b mod m, j+l mod k). Graph: A-vertex g ~ B-vertex s*g for s in S.
# Diameter <= D is checked by full BFS from several sources on both sides (e,A), (e,B) and random extra ones.
import sys, re, random
from collections import deque
sol = sys.argv[1]
lines = open(sol).read().split('\n')
hdr = lines[0].split()
assert hdr[2] == 'meta', hdr
D = int(hdr[1]); m, k, r = int(hdr[3]), int(hdr[4]), int(hdr[5]); N = int(hdr[hdr.index('N') + 1])
S = []
for ln in lines[1:]:
    mm = re.search(r'meta\(a=(\d+),j=(\d+)\)', ln)
    if mm: S.append((int(mm.group(1)), int(mm.group(2))))
assert len(S) == int(hdr[1]) if False else True
d = int(hdr[0]); assert len(S) == d, (len(S), d)
assert m * k == N, (m, k, N)
assert pow(r, k, m) == 1 % m and r % m != 0
rp = [pow(r, j, m) for j in range(k)]
def idx(a, j): return a * k + j
def mul(x, y):  # x=(a,j), y=(b,l)
    return ((x[0] + rp[x[1]] * y[0]) % m, (x[1] + y[1]) % k)
# distinct generators and identity present
assert S[0] == (0, 0), S[0]
assert len(set(S)) == d
Sg = S
# inverse of s
def inv(x):
    j = (-x[1]) % k
    return ((-rp[j] * x[0]) % m, j)
Sinv = [inv(s) for s in Sg]
def bfs(src_side, src):
    # vertices: side 0 = A, side 1 = B; index idx(a,j) on each side
    dist = [[-1] * N, [-1] * N]
    s_side, sg = src_side, src
    dist[s_side][idx(*sg)] = 0
    q = deque([(s_side, sg)])
    while q:
        side, g = q.popleft()
        dg = dist[side][idx(*g)]
        if side == 0:
            nb = [(1, mul(s, g)) for s in Sg]           # A g ~ B s g
        else:
            nb = [(0, mul(si, g)) for si in Sinv]      # B h ~ A s^-1 h
        for ns, ng in nb:
            t = idx(*ng)
            if dist[ns][t] < 0:
                dist[ns][t] = dg + 1
                q.append((ns, ng))
    reached = sum(1 for x in dist[0] if x >= 0) + sum(1 for x in dist[1] if x >= 0)
    ecc = max(max(dist[0]), max(dist[1]))
    return reached, ecc
random.seed(7)
srcs = [(0, (0, 0)), (1, (0, 0))] + [(random.randrange(2), (random.randrange(m), random.randrange(k))) for _ in range(3)]
ok = True
for side, g in srcs:
    reached, ecc = bfs(side, g)
    print(f"src side={'AB'[side]} g={g}: reached {reached}/{2*N} ecc={ecc}")
    if reached != 2 * N or ecc > D: ok = False
print("VALID" if ok else "INVALID", f"d={d} D={D} meta {m} {k} {r} N={N} vertices={2*N}")
