# c8 check: for an opposite flag pair (p1,l1) (base) and (p0,l0) (new type-4 candidate), count
#   cA = #{u point: d(u,p1)=2, d(u,p0)=4, d(u,l0)=5}      (|S'(p0) cap B2(p1)|)
#   cB = #{L line:  d(L,l1)=2, d(L,l0)=4, d(L,p0)=5}      (|S(l0) cap B2(l1)|)
# Type-4 extension of a B2 base needs cA == cB for every base pair. Incidence graph of H(q) from hex_qQ.bin.
import sys, random, struct
from collections import deque
fn = sys.argv[1]
with open(fn, 'rb') as f:
    q, N, _ = struct.unpack('<iii', f.read(12))
    LP = struct.unpack('<%di' % (N * (q + 1)), f.read(4 * N * (q + 1)))
Q1 = q + 1
PL = [[] for _ in range(N)]
for l in range(N):
    for k in range(Q1):
        PL[LP[l * Q1 + k]].append(l)
def bfs(s_isline, s):
    d = [-1] * (2 * N)
    src = N + s if s_isline else s
    d[src] = 0
    dq = deque([src])
    while dq:
        v = dq.popleft(); dv = d[v] + 1
        if v < N:
            for l in PL[v]:
                w = N + l
                if d[w] < 0: d[w] = dv; dq.append(w)
        else:
            for p in LP[(v - N) * Q1:(v - N) * Q1 + Q1]:
                if d[p] < 0: d[p] = dv; dq.append(p)
    return d  # d[0..N) points, d[N..2N) lines
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
p0 = random.randrange(N); l0 = random.choice(PL[p0])
D_p0 = bfs(False, p0); D_l0 = bfs(True, l0)
while True:  # opposite flag (p1,l1): d(p1,p0)=6, d(l1,l0)=6, d(p1,l0)=5, d(p0,l1)=5
    p1 = random.randrange(N); l1 = random.choice(PL[p1])
    if D_p0[p1] == 6 and D_l0[N + l1] == 6 and D_l0[p1] == 5 and D_p0[N + l1] == 5: break
D_p1 = bfs(False, p1); D_l1 = bfs(True, l1)
cA = sum(1 for u in range(N) if D_p1[u] == 2 and D_p0[u] == 4 and D_l0[u] == 5)
cB = sum(1 for L in range(N) if D_l1[N + L] == 2 and D_l0[N + L] == 4 and D_p0[N + L] == 5)
B2p1 = sum(1 for u in range(N) if D_p1[u] == 2)
print("q=%d flags (p0,l0)=(%d,%d) (p1,l1)=(%d,%d)  |B2|=%d  cA=%d  cB=%d" % (q, p0, l0, p1, l1, B2p1, cA, cB))
