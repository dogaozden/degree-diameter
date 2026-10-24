# Replicates haar_sym's PSL(2,q) element enumeration (build_matrix) to map matrices <-> element indices.
# usage: python3 psl_index.py q I [M]   -> prints rep of index I, and index of M^2, M^3, M^4 (M = rep of I by default)
import sys
q = int(sys.argv[1]) if len(sys.argv) > 1 else 71
I = int(sys.argv[2]) if len(sys.argv) > 2 else None
def inv(a): return pow(a, q - 2, q)
idx = {}; rep = []
for t in range(q * q * q):
    a, b, c = t // (q * q), (t // q) % q, t % q
    if a:
        d = inv(a) * (1 + b * c) % q
    else:
        if not b: continue
        d = c; c = (-inv(b)) % q
    key = (a, b, c, d)
    if key in idx: continue
    n = len(rep); rep.append(key)
    idx[key] = n
    idx[((-a) % q, (-b) % q, (-c) % q, (-d) % q)] = n
def mul(X, Y):
    return ((X[0]*Y[0] + X[1]*Y[2]) % q, (X[0]*Y[1] + X[1]*Y[3]) % q,
            (X[2]*Y[0] + X[3]*Y[2]) % q, (X[2]*Y[1] + X[3]*Y[3]) % q)
ident = idx[(1, 0, 0, 1)]
print("classes", len(rep), "identity index", ident)
if I is not None:
    M = rep[I]; print("rep of index", I, "=", "mat(%d,%d,%d,%d)" % M)
    P = M
    for k in range(2, 6):
        P = mul(P, M)
        print("  M^%d = mat(%d,%d,%d,%d) index %d" % (k, P[0], P[1], P[2], P[3], idx[P]))
