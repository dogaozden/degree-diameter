# Bipartite route-chart lift of a Haar controller H(G,S), |S| = 4, with fiber F_4^4.
# Controller vertices (g, side); labels a: (g,A)->(s1 g,B), (h,B)->(s2^-1 h,A); b: same with s3, s4.
# Lift vertex (c, x), x in F_4^4; edges (c,x) ~ (sigma_t(c), A_t x + lam b_t), t in {a, b}, lam in F_4.
# usage: buildlift.py table.txt s1 s2 s3 s4 chart.txt out.edges
import sys, itertools
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def mv(A, x): return tuple((MUL[A[i][0]][x[0]] ^ MUL[A[i][1]][x[1]] ^ MUL[A[i][2]][x[2]] ^ MUL[A[i][3]][x[3]]) for i in range(4))
T = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
n = len(T); e = next(i for i in range(n) if all(T[i][j] == j for j in range(n)))
inv = [next(j for j in range(n) if T[i][j] == e) for i in range(n)]
s = list(map(int, sys.argv[2:6]))
ch = open(sys.argv[6]).read().split()
# chart file: 16 digits A_a (row-major), 4 digits b_a, 16 digits A_b, 4 digits b_b
d = [int(c) for c in ''.join(ch)]
Aa = [d[0:4], d[4:8], d[8:12], d[12:16]]; ba = tuple(d[16:20]); Ab = [d[20:24], d[24:28], d[28:32], d[32:36]]; bb = tuple(d[36:40])
X = list(itertools.product(range(4), repeat=4)); xid = {x: i for i, x in enumerate(X)}
def vid(c, x): return c * 256 + xid[x]   # controller vertex c = side*n + g
def sig(t, c):
    side, g = divmod(c, n)
    if t == 'a': return (n + T[s[0]][g]) if side == 0 else T[inv[s[1]]][g]
    else: return (n + T[s[2]][g]) if side == 0 else T[inv[s[3]]][g]
E = set()
for c in range(2 * n):
    for t, A, b in (('a', Aa, ba), ('b', Ab, bb)):
        dct = sig(t, c)
        for x in X:
            Ax = mv(A, x)
            for lam in range(4):
                y = tuple(Ax[i] ^ MUL[lam][b[i]] for i in range(4))
                u, v = vid(c, x), vid(dct, y)
                E.add((min(u, v), max(u, v)))
N = 2 * n * 256
# relabel so that side A (controller side 0) comes first: already (c < n) -> ids < n*256
with open(sys.argv[7], 'w') as f:
    f.write(f'{N}\n')
    for u, v in sorted(E): f.write(f'{u} {v}\n')
print('vertices', N, 'edges', len(E), file=sys.stderr)
