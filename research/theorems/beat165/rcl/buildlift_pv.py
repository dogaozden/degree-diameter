# Route-chart lift of a permutation-voltage controller with fiber F_4^4.
# Controller vertex (v, g) -> v*m + g, v in [0,2k) (v<k side A); sigma_a(v,g) = (pa[v], fa[v]*g), sigma_b likewise.
# Lift vertex (c, x) -> c*256 + lexicographic index of x; edges (c,x) ~ (sigma_t(c), A_t x + lam b_t), t in {a,b}.
# usage: buildlift_pv.py TABLE CTRLFILE CHARTFILE OUT.edges   (side-A lift vertices are 0 .. k*m*256-1)
import sys, itertools
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def mv(A, x): return tuple((MUL[A[i][0]][x[0]] ^ MUL[A[i][1]][x[1]] ^ MUL[A[i][2]][x[2]] ^ MUL[A[i][3]][x[3]]) for i in range(4))
T = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
m = len(T)
c = list(map(int, open(sys.argv[2]).read().split()))
k = c[0]; nb = 2 * k; assert c[1] == m
pa = c[2:2+nb]; pb = c[2+nb:2+2*nb]; fa = c[2+2*nb:2+3*nb]; fb = c[2+3*nb:2+4*nb]
d = [int(ch) for ch in open(sys.argv[3]).read() if ch in '0123']
Aa = [d[0:4], d[4:8], d[8:12], d[12:16]]; ba = tuple(d[16:20]); Ab = [d[20:24], d[24:28], d[28:32], d[32:36]]; bb = tuple(d[36:40])
X = list(itertools.product(range(4), repeat=4)); xid = {x: i for i, x in enumerate(X)}
E = set()
for v in range(nb):
    for g in range(m):
        cv = v * m + g
        for p, f, A, b in ((pa, fa, Aa, ba), (pb, fb, Ab, bb)):
            dv = p[v] * m + T[f[v]][g]
            for x in X:
                Ax = mv(A, x)
                for lam in range(4):
                    y = tuple(Ax[i] ^ MUL[lam][b[i]] for i in range(4))
                    u, w = cv * 256 + xid[x], dv * 256 + xid[y]
                    E.add((min(u, w), max(u, w)))
N = nb * m * 256
with open(sys.argv[4], 'w') as fo:
    fo.write(f'{N}\n')
    for u, w in sorted(E): fo.write(f'{u} {w}\n')
print('vertices', N, 'edges', len(E), file=sys.stderr)
