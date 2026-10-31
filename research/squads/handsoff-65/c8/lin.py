from g2base import *
import random
def mat(v): return [v[i*N:(i+1)*N] for i in range(N)]
def mm(A, B):
    n = len(A); m = len(B[0]); k = len(B)
    return [[sum(A[i][t] * B[t][j] for t in range(k)) % p for j in range(m)] for i in range(n)]
def madd(A, B, s=1): return [[(A[i][j] + s * B[i][j]) % p for j in range(N)] for i in range(N)]
def ident(): return [[int(i == j) for j in range(N)] for i in range(N)]
def minv(A):
    n = len(A)
    M = [A[i][:] + [int(i == j) for j in range(n)] for i in range(n)]
    for c in range(n):
        pr = next(i for i in range(c, n) if M[i][c] % p)
        M[c], M[pr] = M[pr], M[c]
        inv = pow(M[c][c], p - 2, p)
        M[c] = [(x * inv) % p for x in M[c]]
        for i in range(n):
            if i != c and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[c])]
    return [row[n:] for row in M]
def preserves_phi(g):
    # (g.phi)(a,b,c) = phi(ga,gb,gc) for all basis triples
    for a, b, c in itertools.combinations(range(N), 3):
        # phi(g e_a, g e_b, g e_c) = sum over m1,m2,m3 g[m1][a] g[m2][b] g[m3][c] phi(m1,m2,m3)
        s = 0
        for m1 in range(N):
            if not g[m1][a]: continue
            for m2 in range(N):
                if not g[m2][b]: continue
                for m3 in range(N):
                    if g[m3][c]:
                        s += g[m1][a] * g[m2][b] * g[m3][c] * ph(m1, m2, m3)
        if (s - ph(a, b, c)) % p: return False
    return True
# invariant symmetric form: M symmetric with X^T M + M X = 0 for basis X of g2
def transp(A): return [list(r) for r in zip(*A)]
sym_rows = []
for X in [mat(v) for v in G2basis]:
    # unknown M entries, index i*N+j (use full matrix, equations for all i,j)
    pass
# build linear system over unknowns M[i][j] (i<=j) with symmetric assumption
idx = {}
cnt = 0
for i in range(N):
    for j in range(i, N):
        idx[(i, j)] = cnt; cnt += 1
eqs = []
for X in [mat(v) for v in G2basis]:
    for i in range(N):
        for j in range(N):
            row = [0] * cnt
            # (X^T M)_{ij} = sum_k X[k][i] M[k][j]; (M X)_{ij} = sum_k M[i][k] X[k][j]
            for k in range(N):
                if X[k][i]:
                    key = (min(k, j), max(k, j)); row[idx[key]] += X[k][i]
                if X[k][j]:
                    key = (min(i, k), max(i, k)); row[idx[key]] += X[k][j]
            eqs.append([x % p for x in row])
Bbasis = nullspace(eqs, cnt)
print("invariant symmetric forms:", len(Bbasis))
