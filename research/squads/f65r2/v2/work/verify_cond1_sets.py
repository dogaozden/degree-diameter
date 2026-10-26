# Independent check of the sets reported as satisfying condition 1 (no shared code with search.c):
# group law taken directly from the formula, inverses by search, coverage by all 4-tuples.
import itertools
def mul(p, q):
    x, j = p; y, k = q
    return ((x + pow(8, j, 49) * y) % 49, (j + k) % 7)
G = [(x, j) for x in range(49) for j in range(7)]
def inv(p):
    for q in G:
        if mul(p, q) == (0, 0):
            return q
INV = {g: inv(g) for g in G}
assert len(INV) == 343 and all(mul(g, INV[g]) == (0, 0) for g in G)
# element 0 of the search is (0,0); index i = x + 49*j
def unpack(i): return (i % 49, i // 49)
sets = []
with open('g343_K6_cond1_sets.txt') as f:
    for line in f:
        s = line.split('S=')[1].split(',')
        sets.append([unpack(int(t)) for t in s])
print("cond1 sets read:", len(sets))
min1 = 343; min2 = 343; both = 0; bad = 0
for S in sets:
    assert len(set(S)) == 6 and (0, 0) in S
    D1 = {mul(INV[a], b) for a in S for b in S}
    C1 = {mul(x, y) for x in D1 for y in D1}
    u1 = 343 - len(C1)
    E = [mul(a, INV[b]) for a in S for b in S]
    C2 = {mul(x, y) for x in E for y in E}
    u2 = 343 - len(C2)
    # also the literal 4-fold definitions
    L1 = {mul(mul(INV[x1], x2), mul(INV[x3], x4)) for x1 in S for x2 in S for x3 in S for x4 in S}
    L2 = {mul(mul(x1, INV[x2]), mul(x3, INV[x4])) for x1 in S for x2 in S for x3 in S for x4 in S}
    assert len(L1) == len(C1) and len(L2) == len(C2)
    if u1 != 0: bad += 1
    min1 = min(min1, u1); min2 = min(min2, u2)
    if u1 == 0 and u2 == 0: both += 1
print("cond1 failures among listed sets:", bad)
print("min uncovered cond1 over listed sets:", min1)
print("min uncovered cond2 over listed sets:", min2)
print("listed sets satisfying both:", both)
