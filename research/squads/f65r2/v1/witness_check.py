import itertools
p = 7
def mul(g, h):
    a, b, c = g; a2, b2, c2 = h
    return ((a + a2) % p, (b + b2) % p, (c + c2 + a * b2) % p)
def inv(g):
    for h in itertools.product(range(p), repeat=3):
        if mul(g, h) == (0, 0, 0):
            return h
G = list(itertools.product(range(p), repeat=3))
INV = {g: inv(g) for g in G}
def covered(S):
    Q = {mul(INV[x], y) for x in S for y in S}
    return {mul(q, r) for q in Q for r in Q}
S = [(0,0,0),(1,0,0),(0,1,0),(0,2,2),(1,2,1),(4,4,2)]
unc = [g for g in G if g not in covered(S)]
print("witness |S|=", len(set(S)), "uncovered:", len(unc), unc)
