# Independent diameter check of a Haar graph H(G,S), G = Z_m x|_r Z_k (n = 1 only).
# Group law written here from scratch: (a,j)(b,l) = (a + r^j b mod m, j + l mod k); element index = a*k + j.
# Vertices (g,A),(g,B); edges (g,A)~(s g,B). Right translations are automorphisms, so diameter =
# max(ecc((e,A)), ecc((e,B))) and both BFS must reach every vertex.
import sys
from collections import deque
def main(path):
    lines = [l.split() for l in open(path) if l.strip()]
    h = lines[0]
    d, D = int(h[0]), int(h[1])
    assert h[2] == 'meta', h[2]
    m, k, r = int(h[3]), int(h[4]), int(h[5])
    n = int(h[h.index('n') + 1]); assert n == 1, 'n>1 not supported here'
    S = []
    for ln in lines[1:]:
        mat = ln[1]  # meta(a=A,j=J)
        A = int(mat[mat.index('a=') + 2:mat.index(',j=')]); J = int(mat[mat.index('j=') + 2:-1])
        S.append((A, J))
    assert len(S) == d and len(set(S)) == d
    assert pow(r, k, m) == 1 % m
    Rp = [pow(r, j, m) for j in range(k)]
    def mul(x, y):
        a, j = x; b, l = y
        return ((a + Rp[j] * b) % m, (j + l) % k)
    def inv(x):
        a, j = x
        return ((-pow(r, (k - j) % k, m) * a) % m, (-j) % k)
    # check group axioms on a sample (associativity)
    import random
    for _ in range(2000):
        x = (random.randrange(m), random.randrange(k)); y = (random.randrange(m), random.randrange(k)); z = (random.randrange(m), random.randrange(k))
        assert mul(mul(x, y), z) == mul(x, mul(y, z))
    for s in S:
        assert mul(s, inv(s)) == (0, 0)
    G = m * k
    idx = lambda x: x[0] * k + x[1]
    elems = [(a, j) for a in range(m) for j in range(k)]
    Lmul = [[idx(mul(s, g)) for g in elems] for s in S]      # s*g
    Linv = [[idx(mul(inv(s), g)) for g in elems] for s in S]  # s^-1 * g
    def ecc(src_side):
        dist = [-1] * (2 * G)
        src = src_side * G + 0  # index of e (identity is (0,0) -> index 0)
        dist[src] = 0; q = deque([src]); seen = 1
        while q:
            v = q.popleft(); dv = dist[v] + 1
            if v < G:  # A-vertex g: neighbours (s g, B)
                for T in Lmul:
                    w = G + T[v]
                    if dist[w] < 0: dist[w] = dv; seen += 1; q.append(w)
            else:      # B-vertex g: neighbours (s^-1 g, A)
                g = v - G
                for T in Linv:
                    w = T[g]
                    if dist[w] < 0: dist[w] = dv; seen += 1; q.append(w)
        return seen, max(dist)
    sA, eA = ecc(0); sB, eB = ecc(1)
    ok = (sA == 2 * G and sB == 2 * G and max(eA, eB) <= D)
    print(f"{'VALID' if ok else 'INVALID'} d={d} D={D} group=meta {m} {k} {r} N={2*G} reached=({sA},{sB}) diam_ecc=({eA},{eB})")
    return 0 if ok else 1
if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
