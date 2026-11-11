# analyse.py TAB S1 S2 S3 : for S = {e,S1,S2,S3}, list the uncovered elements of T^{<=4} (side A) and T'^{<=4} (side B)
# with their coset of P (P = elements of order dividing 5) and order; cost = total uncovered.
import sys, numpy as np
raw = open(sys.argv[1], 'rb').read()
N = int(np.frombuffer(raw[:4], dtype=np.int32)[0])
T = np.frombuffer(raw[4:], dtype=np.uint16).reshape(N, N).astype(np.int64)
inv = np.array([int(np.nonzero(T[g] == 0)[0][0]) for g in range(N)])
S = [0] + [int(x) for x in sys.argv[2:5]]
def ball(gens, k):
    cur = {0}
    Tset = sorted({int(T[a, b]) for a in gens for b in gens})
    X = {0}
    Ts = set(gens)
    layer = {0}
    for _ in range(k):
        layer = {int(T[x, t]) for x in layer for t in Tset}
        X |= layer
    return X
Tset = sorted({int(T[inv[s], s2]) for s in S for s2 in S})
Tp = sorted({int(T[s, inv[s2]]) for s in S for s2 in S})
def cover(Tl):
    X = {0}; layer = {0}
    for _ in range(4):
        layer = {int(T[x, t]) for x in layer for t in Tl}
        X |= layer
    return X
XA = cover(Tset); XB = cover(Tp)
unA = [g for g in range(N) if g not in XA]; unB = [g for g in range(N) if g not in XB]
print("T size", len(Tset), "T' size", len(Tp), "uncovered A", len(unA), "uncovered B", len(unB), "cost", len(unA) + len(unB))
ords = {}
def order(g):
    k, x = 1, g
    while x != 0:
        x = T[x, g]; k += 1
    return k
P = [g for g in range(N) if order(g) in (1, 5)]
print("P size", len(P))
def cosetP(g):
    # index k with g in P t^k where t has order 4
    t = [h for h in range(N) if order(h) == 4][0]
    tk = [0, t, int(T[t, t]), int(T[int(T[t, t]), t])]
    for k in range(4):
        if int(T[g, inv[tk[k]]]) in set(P): return k
    return -1
print("uncovered A (element: order, coset of P, central):")
for g in unA[:40]:
    print("  A", g, order(g), cosetP(g), bool(np.all(T[g] == T[:, g])))
print("uncovered B:")
for g in unB[:40]:
    print("  B", g, order(g), cosetP(g), bool(np.all(T[g] == T[:, g])))
