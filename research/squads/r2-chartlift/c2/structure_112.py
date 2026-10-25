"""Quick structure report for a k=5, q=3 chart file (A_c 16 entries row-major, then b_c): orders, commuting pairs,
parallel b-pairs.  Pure arithmetic over F_3; not a search."""
import sys, itertools
Q = 3
def mat(v): return tuple(tuple(v[4 * r:4 * r + 4]) for r in range(4))
def mul(X, Y): return tuple(tuple(sum(X[r][t] * Y[t][c] for t in range(4)) % Q for c in range(4)) for r in range(4))
I = tuple(tuple(int(r == c) for c in range(4)) for r in range(4))
def order(X):
    Y, n = X, 1
    while Y != I:
        Y = mul(Y, X); n += 1
        if n > 200: return None
    return n
def parallel(u, v):
    return all((u[i] * v[j] - u[j] * v[i]) % Q == 0 for i in range(4) for j in range(4))
rows = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
A = [mat(rows[c]) for c in range(5)]; b = [tuple(rows[5 + c]) for c in range(5)]
print('A_0 is identity:', A[0] == I)
print('orders of A_c:', [order(A[c]) for c in range(5)])
print('commuting pairs among A_1..A_4:', [(c, d) for c in range(1, 5) for d in range(c + 1, 5) if mul(A[c], A[d]) == mul(A[d], A[c])])
print('parallel b pairs:', [(c, d) for c in range(5) for d in range(c + 1, 5) if parallel(b[c], b[d])])
print('b vectors:', b)
