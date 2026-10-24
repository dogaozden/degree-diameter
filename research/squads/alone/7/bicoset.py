"""Bi-coset graphs of G = SL(2,64) (wildcard family, generalises Haar graphs: A = B = 1 gives a Haar graph).

Subgroups A, B of order 16 inside the unipotent radical U = {[[1,t],[0,1]]} (t in a 4-dim F2-subspace of GF(64)).
Right cosets Ag (A-side) and Bh (B-side); Ag ~ Bh iff g h^-1 in D = A x B, with x in G fixed.
Degree = |A : A cap x B x^-1| (16 iff the intersection is trivial). Right multiplication by G is an automorphism
group transitive on each side, so diameter = max(ecc(A.1), ecc(B.1)) (both BFS from the identity cosets).

Neighbours (derived from D = A x B):  Ag ~ B.(x^-1 a g) for a in A;  Bh ~ A.(x b h) for b in B.

usage: python3 bicoset.py SEED [TRIES] [OUTEDGES]
"""
import random
import sys
from collections import deque

# ---- GF(64) with modulus x^6 + x + 1 (x is primitive): elements are ints 0..63
MOD = 0b1000011
EXP, LOG = [0] * 128, [0] * 64
v = 1
for i in range(63):
    EXP[i] = v
    LOG[v] = i
    v <<= 1
    if v & 64:
        v ^= MOD
for i in range(63, 128):
    EXP[i] = EXP[i - 63]
MUL = [[0] * 64 for _ in range(64)]
for a in range(1, 64):
    for b in range(1, 64):
        MUL[a][b] = EXP[LOG[a] + LOG[b]]

def mat(a, b, c, d):
    return (a, b, c, d)

def mmul(X, Y):
    a, b, c, d = X
    e, f, g, h = Y
    m = MUL
    return (m[a][e] ^ m[b][g], m[a][f] ^ m[b][h], m[c][e] ^ m[d][g], m[c][f] ^ m[d][h])

def minv(X):           # det 1 in characteristic 2: inverse is [[d,b],[c,a]]
    a, b, c, d = X
    return (d, b, c, a)

def span(basis):
    s = {0}
    for v in basis:
        s |= {x ^ v for x in s}
    return sorted(s)

def rand_sl(rng):
    while True:
        a, b, c, d = (rng.randrange(64) for _ in range(4))
        if MUL[a][d] ^ MUL[b][c] == 1:
            return (a, b, c, d)

def bfs_ecc(start, nbr):
    dist = {start: 0}
    dq = deque([start])
    while dq:
        u = dq.popleft()
        for w in nbr(u):
            if w not in dist:
                dist[w] = dist[u] + 1
                dq.append(w)
    return dist

def run(VA, VB, x, verbose=False):
    A = [(1, t, 0, 1) for t in span(VA)]
    B = [(1, t, 0, 1) for t in span(VB)]
    xi = minv(x)
    # A cap x B x^-1 must be trivial for degree 16
    inter = [mmul(mmul(x, b), xi) for b in B]
    if sum(1 for y in inter if y in set(A)) != 1:
        return None
    def keyA(g):
        return min(mmul(a, g) for a in A)
    def keyB(g):
        return min(mmul(b, g) for b in B)
    # representatives: keys are canonical; we need a representative to continue BFS
    def nbrs(node):
        side, g = node
        if side == 'A':
            out = {('B', keyB(mmul(mmul(xi, a), g))) for a in A}
            return out
        out = {('A', keyA(mmul(mmul(x, b), g))) for b in B}
        return out
    # BFS over canonical keys; a key itself is a valid representative of its coset
    start = ('A', keyA((1, 0, 0, 1)))
    dist = {start: 0}
    dq = deque([start])
    degs = set()
    while dq:
        u = dq.popleft()
        nb = nbrs(u)
        degs.add(len(nb))
        for w in nb:
            if w not in dist:
                dist[w] = dist[u] + 1
                dq.append(w)
    n_total = len(dist)
    ecc_A = max(dist.values())
    # B-source
    startB = ('B', keyB((1, 0, 0, 1)))
    distB = {startB: 0}
    dq = deque([startB])
    while dq:
        u = dq.popleft()
        for w in nbrs(u):
            if w not in distB:
                distB[w] = distB[u] + 1
                dq.append(w)
    ecc_B = max(distB.values())
    return dict(n_reached=n_total, nB_reached=len(distB), ecc_A=ecc_A, ecc_B=ecc_B, degrees=sorted(degs))

if __name__ == '__main__':
    seed = int(sys.argv[1]); tries = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rng = random.Random(seed)
    for t in range(tries):
        while True:
            VA = []
            while len(span(VA)) < 16:
                cand = rng.randrange(1, 64)
                if cand not in span(VA):
                    VA.append(cand)
                if len(VA) > 4:
                    VA = []
            VB = []
            while len(span(VB)) < 16:
                cand = rng.randrange(1, 64)
                if cand not in span(VB):
                    VB.append(cand)
                if len(VB) > 4:
                    VB = []
            break
        x = rand_sl(rng)
        res = run(VA, VB, x)
        print(t, 'VA', VA, 'VB', VB, 'x', x, res, flush=True)


def far_counts(VA, VB, x, radius=5):
    """vertices farther than radius from A.1 plus from B.1; None if the graph is not a valid 16-regular connected graph"""
    res = run_full(VA, VB, x, radius)
    return res

def run_full(VA, VB, x, radius):
    A = [(1, t, 0, 1) for t in span(VA)]
    B = [(1, t, 0, 1) for t in span(VB)]
    xi = minv(x)
    Aset = set(A)
    if sum(1 for b in B if mmul(mmul(x, b), xi) in Aset) != 1:
        return None
    def keyA(g):
        return min(mmul(a, g) for a in A)
    def keyB(g):
        return min(mmul(b, g) for b in B)
    def nbrs(node):
        side, g = node
        if side == 'A':
            return {('B', keyB(mmul(mmul(xi, a), g))) for a in A}
        return {('A', keyA(mmul(mmul(x, b), g))) for b in B}
    total = 0
    for start in (('A', keyA((1, 0, 0, 1))), ('B', keyB((1, 0, 0, 1)))):
        dist = {start: 0}
        dq = deque([start])
        degs = set()
        while dq:
            u = dq.popleft()
            nb = nbrs(u)
            degs.add(len(nb))
            for w in nb:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    dq.append(w)
        if len(dist) != 32760 or degs != {16}:
            return None
        total += sum(1 for d in dist.values() if d > radius)
    return total
