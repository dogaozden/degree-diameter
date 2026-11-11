# Independent checker for zpk solution files: Haar graph H(G,S), G = F_p^2 x| Z_k with M = companion matrix of
# (x - z)(x - z^J) (z = a primitive k-th root of 1 in F_p, computed here from scratch).
# Element = (t, (a, b)); product (t1,v1)(t2,v2) = (t1+t2, v1 + M^t1 v2), computed with explicit matrices.
# Checks: M^k = I, group law associativity on random triples, |S| distinct, graph simple and DEG-regular,
# and BFS eccentricity of (e,0) and (e,1) in the bipartite graph (vertex-transitive on each side) <= D.
import sys, random
from collections import deque

def main(path, Dclaim=None):
    lines = open(path).read().split("\n")
    P, K, J, DEG, D = map(int, lines[0].split())
    S = [tuple(map(int, lines[1 + i].split())) for i in range(DEG)]
    # primitive k-th root of unity
    def is_root(c):
        if pow(c, K, P) != 1: return False
        for q in range(2, K + 1):
            if K % q == 0 and all(q % d for d in range(2, int(q ** 0.5) + 1)) and pow(c, K // q, P) == 1:
                return False
        return True
    z = next(pow(h, (P - 1) // K, P) for h in range(2, P) if is_root(pow(h, (P - 1) // K, P)))
    al, be = z, pow(z, J, P)
    assert al != be
    M = [[0, (-al * be) % P], [1, (al + be) % P]]
    def mm(A, B):
        return [[(A[i][0] * B[0][j] + A[i][1] * B[1][j]) % P for j in range(2)] for i in range(2)]
    Mp = [[[1, 0], [0, 1]]]
    for t in range(1, K + 1):
        Mp.append(mm(Mp[-1], M))
    assert Mp[K] == [[1, 0], [0, 1]], "M^K != I"
    def mv(A, v):
        return ((A[0][0] * v[0] + A[0][1] * v[1]) % P, (A[1][0] * v[0] + A[1][1] * v[1]) % P)
    def mul(g, h):
        t1, v1 = g; t2, v2 = h
        w = mv(Mp[t1 % K], v2)
        return ((t1 + t2) % K, ((v1[0] + w[0]) % P, (v1[1] + w[1]) % P))
    e = (0, (0, 0))
    def inv(g):
        t, v = g
        w = mv(Mp[(-t) % K], v)
        return ((-t) % K, ((-w[0]) % P, (-w[1]) % P))
    rng = random.Random(1)
    def rel():
        return ((rng.randrange(K)), (rng.randrange(P), rng.randrange(P)))
    for _ in range(2000):
        a, b, c = rel(), rel(), rel()
        assert mul(mul(a, b), c) == mul(a, mul(b, c)), "associativity"
        assert mul(a, inv(a)) == e
    Sg = [tuple(s[0:1]) + ((s[1], s[2]),) for s in S]
    assert len(set(Sg)) == DEG, "S not distinct"
    Ginv = [inv(s) for s in Sg]
    G = K * P * P
    NV = 2 * G
    def vid(g, side):
        t, (a, b) = g
        return ((t * P + a) * P + b) * 2 + side
    def elt(i):
        side = i & 1; g = i >> 1
        b = g % P; g //= P; a = g % P; t = g // P
        return (t, (a, b))
    dist = [-1] * NV
    worst = 0
    for src_side in (0, 1):
        dist = [-1] * NV
        s0 = vid(e, src_side)
        dist[s0] = 0
        q = deque([s0])
        while q:
            x = q.popleft()
            d = dist[x]
            g = elt(x)
            side = x & 1
            nbrs = []
            for s in (Sg if side == 0 else Ginv):
                h = mul(g, s)
                nbrs.append(vid(h, 1 - side))
            if side == 0:
                pass
            assert len(set(nbrs)) == DEG, "not simple/regular"
            for y in nbrs:
                if dist[y] < 0:
                    dist[y] = d + 1
                    q.append(y)
        unreached = sum(1 for x in dist if x < 0)
        ecc = max(dist)
        worst = max(worst, ecc)
        print(f"source side {src_side}: ecc={ecc} unreached={unreached}")
        assert unreached == 0
    # bipartiteness check for the flip-side edges is implicit in construction
    ok = worst <= D
    print(f"N={NV} |G|={G} P={P} K={K} J={J} DEG={DEG} D={D} maxecc={worst} VALID={ok}")
    return NV, ok

if __name__ == "__main__":
    main(sys.argv[1])
