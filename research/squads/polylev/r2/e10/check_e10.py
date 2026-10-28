"""Independent scorer for card e10 (no code shared with the builder).
usage: check_e10.py PCOL LCOL   (int32 per point/line of H(3), class index or -1)
Checks on H(3) read from hex_q3.bin (q=3, so field arithmetic is mod 3):
 - every coloured point class has 4 points, all on Q(6,3), pairwise orthogonal, spanning rank 2
   (a totally singular line of Q(6,3)); classes pairwise disjoint;
 - every line class has 4 lines, pairwise disjoint; |A_i| == |B_i| for all i;
 - every class meets the incidence-graph 4-ball of every point (resp. every line).
Prints the number of point classes and line classes that are valid and the number of classes that meet all balls.
"""
import sys, struct
from collections import deque
import numpy as np

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q3.bin'
q = 3

with open(HEX, 'rb') as f:
    qq, N, L = struct.unpack('<3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (qq + 1)), dtype='<i4').reshape(L, qq + 1).astype(np.int64)
    X = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
assert qq == q and N == 364 and L == 364

# quadric and polar form over GF(3)
def Qf(x):
    return (x[0] * x[4] + x[1] * x[5] + x[2] * x[6] - x[3] * x[3]) % 3
def bf(x, y):
    return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3
def rank3(M):
    M = [list(map(int, r)) for r in M]
    r = 0
    cols = len(M[0])
    for c in range(cols):
        piv = next((i for i in range(r, len(M)) if M[i][c] % 3), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = 1 if M[r][c] % 3 == 1 else 2
        M[r] = [(v * inv) % 3 for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % 3:
                f = M[i][c]
                M[i] = [(a - f * b) % 3 for a, b in zip(M[i], M[r])]
        r += 1
    return r

assert all(Qf(X[p]) == 0 for p in range(N)), 'points not on Q'

# incidence graph distances (points 0..N-1, lines N..N+L-1)
adj = [[] for _ in range(N + L)]
for l in range(L):
    for p in lines[l]:
        adj[int(p)].append(N + l)
        adj[N + l].append(int(p))
D = np.zeros((N + L, N + L), dtype=np.int64)
for s in range(N + L):
    dist = [-1] * (N + L); dist[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1; dq.append(w)
    D[s] = dist
assert (D >= 0).all(), 'incidence graph disconnected'
# sanity: two points are within incidence distance 4 iff they are orthogonal
M = np.array([[bf(X[p], X[x]) == 0 for x in range(N)] for p in range(N)])
assert ((D[:N, :N] <= 4) == M).all(), 'distance/orthogonality mismatch'

pcol = np.fromfile(sys.argv[1], dtype='<i4')
lcol = np.fromfile(sys.argv[2], dtype='<i4')
assert len(pcol) == N and len(lcol) == L

def class_sets(col):
    out = {}
    for v in range(N):
        if col[v] >= 0:
            out.setdefault(int(col[v]), []).append(v)
    return out

PC = class_sets(pcol); LC = class_sets(lcol)
print('point classes', len(PC), 'uncoloured points', int((pcol < 0).sum()),
      'sizes', sorted(set(len(v) for v in PC.values())))
print('line classes', len(LC), 'uncoloured lines', int((lcol < 0).sum()),
      'sizes', sorted(set(len(v) for v in LC.values())))
ids = sorted(set(PC) | set(LC))
bad_size = [i for i in ids if len(PC.get(i, [])) != len(LC.get(i, []))]
print('colours with |A_i| != |B_i|:', len(bad_size), bad_size[:10])

# totally singular check for points: the class must contain 4 points that are pairwise orthogonal, rank 2
# (a totally singular line of Q(6,3)); extra points added by balancing may lie outside it
from itertools import combinations
def has_ts_line(A):
    for T in combinations(A, 4):
        if all(bf(X[a], X[b]) == 0 for a in T for b in T) and rank3(X[list(T)]) == 2:
            return True
    return False
ts_ok = {i: has_ts_line(A) for i, A in PC.items()}
print('point classes containing a totally singular line:', sum(ts_ok.values()), 'of', len(PC))
# lines: 4 lines each, pairwise disjoint: check point sets of lines
def line_ok(i):
    return len(LC.get(i, [])) == 4
print('line classes of size >= 4:', sum(len(LC.get(i, [])) >= 4 for i in LC))

# disjointness of the point classes (by construction of colour files, check anyway)
seen = {}
dup = 0
for i, A in PC.items():
    for a in A:
        if a in seen:
            dup += 1
        seen[a] = i
print('point duplicates across classes:', dup)
seenl = {}; dupl = 0
for i, B in LC.items():
    for b in B:
        dupl += (b in seenl); seenl[b] = i
print('line duplicates across classes:', dupl)

# 4-ball check: each class meets the 4-ball of every point / line
pt_ball = {i: bool((D[:N][:, A].min(axis=1) <= 4).all()) for i, A in PC.items()}
ln_ball = {i: bool((D[N:][:, [N + b for b in B]].min(axis=1) <= 4).all()) for i, B in LC.items()}
print('point classes meeting every 4-ball of a point:', sum(pt_ball.values()), 'of', len(PC))
print('line classes meeting every 4-ball of a line:', sum(ln_ball.values()), 'of', len(LC))
both = [i for i in ids if pt_ball.get(i, False) and ln_ball.get(i, False)]
print('colours where both sides meet all 4-balls:', len(both))
