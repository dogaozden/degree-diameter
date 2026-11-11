# Fibre-level walk counts of the F5 chart with dropped scalars (voltages ignored): per target, number of walks of length <= 5.
import sys, itertools
import numpy as np
P = 5
base = "/home/user/degree-diameter/research/squads/beyond-small/r1/c08/chart5_s11.txt"
v = [int(x) for x in open(base).read().split()]
A = [np.array(v[16*c:16*c+16]).reshape(4, 4) for c in range(4)]
b = [np.array(v[64+4*c:64+4*c+4]) for c in range(4)]
BI = [0,0,0,1,1,1,2,2,2,0,1,2]; BJ = [0,1,2,0,1,2,0,1,2,0,1,2]; BC = [0,1,2,1,2,0,2,0,1,3,3,3]
full = int(sys.argv[1]); drop = [int(x) for x in sys.argv[2].split(',')]
NF = 625
def xid(x): return x[0] + 5*x[1] + 25*x[2] + 125*x[3]
fibs = [np.array([t % 5, (t//5) % 5, (t//25) % 5, t//125]) for t in range(NF)]
# Gamma on 6*625 vertices: A(i,x) = i*625+x, B(j,y) = 1875 + j*625 + y
n = 6 * NF
adj = [[] for _ in range(n)]
for e in range(12):
    i, j, c = BI[e], BJ[e], BC[e]
    for t in range(NF):
        x = fibs[t]
        for lam in range(5):
            if c != full and drop[c] >= 0 and lam == drop[c]: continue
            y = (A[c] @ x + lam * b[c]) % P
            u = i*NF + t; w = 3*NF + j*NF + xid(y)
            adj[u].append(w); adj[w].append(u)
def walks(src):
    cnt = np.zeros(n, dtype=object); cnt[src] = 1
    tot = cnt.copy()
    for _ in range(5):
        new = np.zeros(n, dtype=object)
        for u in range(n):
            if cnt[u]:
                for w in adj[u]: new[w] += cnt[u]
        cnt = new; tot = tot + cnt
    return tot
for src in (0, 3*NF):
    tot = walks(src)
    side = range(0, 3*NF) if src < 3*NF else range(3*NF, n)
    vals = [tot[u] for u in range(n) if (u < 3*NF) == (src < 3*NF)]
    other = [tot[u] for u in range(n) if (u < 3*NF) != (src < 3*NF)]
    print('src', src, 'same-side min', min(vals), 'median', sorted(vals)[len(vals)//2], 'other-side min', min(other), 'median', sorted(other)[len(other)//2])
