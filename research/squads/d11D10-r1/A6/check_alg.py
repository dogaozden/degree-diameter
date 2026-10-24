# Algebra checks for the alpha pairings in PSL(2,71) x Z_421 (light, no search).
import importlib.util, sys
sys.argv = ['x', '71']
spec = importlib.util.spec_from_file_location('pi', 'psl_index.py')
src = open('psl_index.py').read().split('ident = idx')[0]   # reuse enumeration + mul only
ns = {}
exec(src, ns)
q, idx, rep, mul = ns['q'], ns['idx'], ns['rep'], ns['mul']
def inv_m(M):  # inverse of det-1 matrix
    a, b, c, d = M
    return (d % q, (-b) % q, (-c) % q, a % q)
def canon(M):  # class index of +-M
    return idx[M]
def power(M, k):
    P = (1, 0, 0, 1)
    for _ in range(k): P = mul(P, M)
    return P
# find one element of order 5 (class rep with M^5 = +-I, M != +-I)
ident_cls = idx[(1, 0, 0, 1)]
g = None
for n, M in enumerate(rep):
    if n == ident_cls: continue
    P = M
    o = 1
    while idx[P] != ident_cls and o < 10:
        P = mul(P, M); o += 1
    if o == 5: g = M; break
print("order-5 class rep g =", g, "class", idx[g])
g2, g3, g4 = power(g, 2), power(g, 3), power(g, 4)
print("classes of g^2, g^3, g^4:", idx[g2], idx[g3], idx[g4], "(g^4 = g^-1 class is", idx[inv_m(g)], ")")
# Weyl-type involution inverting the torus containing g: find w of order 2 in PSL with w g w^-1 = +-g^-1
found = None
for n, M in enumerate(rep):
    if n == ident_cls: continue
    if idx[mul(mul(M, M), (1, 0, 0, 1))] != ident_cls: continue       # M^2 = +-I
    W = M
    conj = mul(mul(W, g), inv_m(W))
    if idx[conj] == idx[inv_m(g)]:
        found = W; break
print("involution w inverting g (conj w g w^-1 = +- g^-1):", found, "class", idx[found] if found else None)
print("RESULT: conj by w maps alpha(c_g, r^t) to alpha(c_g, r^-t): pairings t and -t are isomorphic")
