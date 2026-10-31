# Build G2(5) 7-dim rep over F5, the split Cayley hexagon H(5) and its incidence graph.
import itertools, random, sys
p = 5
N = 7
phi = {}
def addt(t, s):
    # sorted triple with sign
    a = list(t); sign = 1
    # bubble sort
    for i in range(3):
        for j in range(2 - i):
            if a[j] > a[j+1]:
                a[j], a[j+1] = a[j+1], a[j]; sign = -sign
    phi[tuple(a)] = (sign * s) % p
for t, s in [((0,1,2),1),((0,3,4),1),((0,5,6),1),((1,3,5),1),((1,4,6),-1),((2,3,6),-1),((2,4,5),-1)]:
    addt(t, s)
def ph(a, b, c):
    idx = [a, b, c]
    if len(set(idx)) < 3: return 0
    s = sorted(range(3), key=lambda i: idx[i])
    srt = tuple(idx[i] for i in s)
    # sign of permutation s
    perm = list(s); sign = 1
    for i in range(3):
        for j in range(2 - i):
            if perm[j] > perm[j+1]:
                perm[j], perm[j+1] = perm[j+1], perm[j]; sign = -sign
    return (sign * phi.get(srt, 0)) % p

def nullspace(rows, ncols):
    # rows: list of lists mod p. returns basis of nullspace
    M = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = None
        for i in range(r, len(M)):
            if M[i][c] % p: pr = i; break
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(x - f * y) % p for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == len(M): break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * ncols; v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][fc]) % p
        basis.append(v)
    return basis

# g2 = {X : sum_m X[m][a] phi(m,b,c) + X[m][b] phi(a,m,c) + X[m][c] phi(a,b,m) = 0}
# unknown X[i][j] index i*N+j ; (X e_j)^i = X[i][j]
rows = []
for a, b, c in itertools.combinations(range(N), 3):
    row = [0] * (N * N)
    for m in range(N):
        # term X(e_a) contributes: phi(X e_a, e_b, e_c) = sum_m X[m][a] phi(m,b,c)
        row[m * N + a] += ph(m, b, c)
        row[m * N + b] += ph(a, m, c)
        row[m * N + c] += ph(a, b, m)
    rows.append([x % p for x in row])
G2basis = nullspace(rows, N * N)
print("dim g2 =", len(G2basis))
