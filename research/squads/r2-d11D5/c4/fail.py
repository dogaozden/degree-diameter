"""Bitset mirror of plusopt2.c total(): returns the list of failing (s, t, coset) triples.
Vertices: points 0..n-1, lines n..2n-1.  Usage: python3 fail.py base.in [sigma-file]  (sigma file: n lines)"""
import sys
def load(path, sig_path=None):
    f = open(path); n, dg = map(int, f.readline().split())
    ln = [list(map(int, f.readline().split())) for _ in range(n)]
    sig = [int(f.readline()) for _ in range(n)]
    f.close()
    if sig_path:
        sig = [int(v) for v in open(sig_path).read().split()][:n]
    return n, dg, ln, sig
def build(n, dg, ln, sig):
    pt = [[] for _ in range(n)]
    for l in range(n):
        for p in ln[l]: pt[p].append(l)
    sinv = [0] * n
    for i in range(n): sinv[sig[i]] = i
    V = 2 * n
    # neighbours (pure) and the single jump neighbour per vertex
    pure = [None] * V; jump = [0] * V
    for x in range(V):
        if x < n: pure[x] = [n + l for l in pt[x]]; jump[x] = n + sig[x]
        else: pure[x] = [p for p in ln[x - n]]; jump[x] = sinv[x - n]
    return V, pure, jump
def failing(n, dg, ln, sig, want_list=True):
    V, pure, jump = build(n, dg, ln, sig)
    full = (1 << V) - 1
    C1 = [[0] * V for _ in range(6)]; C2 = [[0] * V for _ in range(6)]
    for x in range(V): C1[0][x] = 1 << x
    for d in range(1, 6):
        for x in range(V):
            s1 = 0; s2 = 0
            for y in pure[x]:
                b1 = C1[d - 1][y]; b2 = C2[d - 1][y]
                s2 |= b2 | (s1 & b1); s1 |= b1
            C1[d][x] = s1; C2[d][x] = s2
    # jumped reachability, frontier F[x][c] = sources of walks of length d with >=1 jump, coset c
    R = [[0, 0, 0] for _ in range(V)]
    F = [[0, 0, 0] for _ in range(V)]
    for d in range(1, 6):
        N = [[0, 0, 0] for _ in range(V)]
        for x in range(V):
            a0, a1, a2 = F[x]
            if a0 | a1 | a2:
                for y in pure[x]:
                    N[y][0] |= a0; N[y][1] |= a1; N[y][2] |= a2
            a0 |= C1[d - 1][x]
            y = jump[x]
            if x < n:   # point -> line : coset +1
                N[y][1] |= a0; N[y][2] |= a1; N[y][0] |= a2
            else:       # line -> point : coset -1
                N[y][2] |= a0; N[y][0] |= a1; N[y][1] |= a2
        for x in range(V):
            for c in range(3): R[x][c] |= N[x][c]
        F = N
    fails = []; cost = 0
    for t in range(V):
        ok0 = R[t][0] | C1[0][t] | C1[2][t] | C2[4][t] | C2[5][t]
        for c, okc in ((0, ok0), (1, R[t][1]), (2, R[t][2])):
            bad = full & ~okc
            cost += bin(bad).count('1')
            if want_list and bad:
                s = 0
                while bad:
                    if bad & 1: fails.append((s, t, c))
                    bad >>= 1; s += 1
    return cost, fails
if __name__ == '__main__':
    n, dg, ln, sig = load(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)
    cost, fails = failing(n, dg, ln, sig)
    print("cost", cost)
    for s, t, c in fails:
        print("fail s=%d (%s) t=%d (%s) coset=%d" % (s, 'pt' if s < n else 'ln', t, 'pt' if t < n else 'ln', c))
