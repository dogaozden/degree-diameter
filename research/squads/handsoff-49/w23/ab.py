# ab.py TAB S1 S2 S3 : abelianization map psi: G -> G/G' and the psi-values of S, of T^{<=4} sides, and of uncovered elements
import sys, numpy as np
raw = open(sys.argv[1], 'rb').read()
N = int(np.frombuffer(raw[:4], dtype=np.int32)[0])
T = np.frombuffer(raw[4:], dtype=np.uint16).reshape(N, N).astype(np.int64)
X = np.arange(N)
inv = np.array([int(np.nonzero(T[g] == 0)[0][0]) for g in range(N)])
# all commutators [x,y] = x y x^-1 y^-1
comm = set()
for x in range(N):
    c = T[T[T[x, X], inv[x]], inv[X]]  # x y x^-1 y^-1 for all y : (x*y)*x^-1 then * y^-1
    comm.update(np.unique(c).tolist())
gens = sorted(comm)
H = {0}; fr = [0]
while fr:
    nf = []
    for h in fr:
        for g in gens:
            y = int(T[h, g])
            if y not in H:
                H.add(y); nf.append(y)
    fr = nf
print("|G'| =", len(H))
# coset labels of G/G': label = min element of coset
lab = -np.ones(N, dtype=np.int64)
cosets = []
for g in range(N):
    if lab[g] >= 0: continue
    cs = [int(T[g, h]) for h in H]
    for c in cs: lab[c] = len(cosets)
    cosets.append(g)
print("G/G' order", len(cosets))
# cyclic? find order of image of each coset representative
def image_order(k):
    g = cosets[k]; x = g; n = 1
    while lab[x] != lab[0]:
        x = T[x, g]; n += 1
    return n
print("orders of G/G' elements:", sorted(set(image_order(k) for k in range(len(cosets)))))
S = [0] + [int(x) for x in sys.argv[2:5]]
psiS = sorted(set(int(lab[s]) for s in S))
print("psi(S) labels", [int(lab[s]) for s in S])
# Z_20 coordinates: generator u = element with image order 20
u = [cosets[k] for k in range(len(cosets)) if image_order(k) == 20][0]
coord = -np.ones(N, dtype=np.int64)
x = 0
for j in range(20):
    for h in H:
        coord[int(T[x, h])] = j
    x = int(T[x, u])
print("Z20 coords of S:", [int(coord[s]) for s in S])
import itertools
def zsums(vals, k):
    cur = {0}; allv = {0}
    for _ in range(k):
        cur = {(c + v) % 20 for c in cur for v in vals}
        allv |= cur
    return allv
Tc = sorted({int((coord[int(T[inv[s], s2])])) for s in S for s2 in S})
Tpc = sorted({int((coord[int(T[s, inv[s2]])])) for s in S for s2 in S})
print("psi(T) =", Tc, " psi(T') =", Tpc)
print("sums of <=4 from psi(T):", sorted(zsums(Tc, 4)))
print("sums of <=4 from psi(T'):", sorted(zsums(Tpc, 4)))
for g in [int(a) for a in sys.argv[5:]]:
    print("elt", g, "coord", int(coord[g]), "order", image_order(lab[g]) if False else "")
