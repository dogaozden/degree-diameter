# Route-chart lift with per-base-vertex charts (from fitqv's VCHART line), fiber F_4^4.
# Controller vertex (v, g) -> v*m + g; sigma_a(v,g) = (pa[v], fa[v]*g), sigma_b(v,g) = (pb[v], fb[v]*g).
# Base vertex v uses (A_{v,a}, b_{v,a}) on its a-edge and (A_{v,b}, b_{v,b}) on its b-edge.
# Lift vertex (c, x) -> c*256 + index(x), x in lexicographic order of F_4^4 (index = sum x_i 4^i, as in fitqv).
# usage: buildlift_pvv.py TABLE PVCTRL VCHARTFILE OUT.edges
import sys, itertools
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
T = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
m = len(T)
c = list(map(int, open(sys.argv[2]).read().split())); k = c[0]; nb = 2 * k
pa = c[2:2+nb]; pb = c[2+nb:2+2*nb]; fa = c[2+2*nb:2+3*nb]; fb = c[2+3*nb:2+4*nb]
tok = open(sys.argv[3]).read().split()
i0 = tok.index('VCHART'); assert int(tok[i0+1]) == nb
charts = tok[i0+2:i0+2+2*nb]   # order: v0 a, v0 b, v1 a, v1 b, ...
def parse(s):
    A, b = s.split(':'); d = [int(ch) for ch in A]; return [d[0:4], d[4:8], d[8:12], d[12:16]], [int(ch) for ch in b]
CH = [[parse(charts[2*v]), parse(charts[2*v+1])] for v in range(nb)]
def idx(x): return x[0] + 4*x[1] + 16*x[2] + 64*x[3]
def mv(A, x): return [MUL[A[i][0]][x[0]] ^ MUL[A[i][1]][x[1]] ^ MUL[A[i][2]][x[2]] ^ MUL[A[i][3]][x[3]] for i in range(4)]
X = [list(t) for t in itertools.product(range(4), repeat=4)]
E = set()
for v in range(nb):
    for g in range(m):
        cv = v * m + g
        for t, (p, f) in enumerate(((pa, fa), (pb, fb))):
            A, b = CH[v][t]
            dv = p[v] * m + T[f[v]][g]
            for x in X:
                Ax = mv(A, x)
                for lam in range(4):
                    y = [Ax[i] ^ MUL[lam][b[i]] for i in range(4)]
                    u, w = cv * 256 + idx(x), dv * 256 + idx(y)
                    E.add((min(u, w), max(u, w)))
N = nb * m * 256
with open(sys.argv[4], 'w') as fo:
    fo.write(f'{N}\n')
    for u, w in sorted(E): fo.write(f'{u} {w}\n')
print('vertices', N, 'edges', len(E), file=sys.stderr)
