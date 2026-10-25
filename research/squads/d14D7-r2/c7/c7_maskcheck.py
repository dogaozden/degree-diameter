#!/usr/bin/env python3
# c7_maskcheck.py GHFILE SEED NCAND : one matching only. Compares two acceptance rules for units (p, l), l through p:
#  OLD: zones {p} u W and {l} u K pairwise disjoint (t2design/pack rule), freed points outside all W, freed lines outside all K.
#  NEW (pilot, NOT diameter-checked): same freed-point conditions, but W's and K's may overlap. A sigma with
#       sigma(W_u) = K_u, sigma(p_u) = l_u for all u exists iff, for every mask M (set of units), the number of
#       non-freed points whose W-membership set is M equals the number of non-freed lines whose K-membership set is M.
#  W_u = points collinear with p off l (q^2), K_u = lines meeting l off p (q^2). Output: greedy counts under both rules.
import sys, random, collections
gh, seed, ncand = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
with open(gh) as f:
    P, q = map(int, f.readline().split())
    LP = [list(map(int, f.readline().split())) for _ in range(P)]
PL = [[] for _ in range(P)]
for l in range(P):
    for p in LP[l]:
        PL[p].append(l)
def zones(p, l):
    W = set(w for L in PL[p] if L != l for w in LP[L] if w != p)
    K = set(M for x in LP[l] if x != p for M in PL[x] if M != l)
    return W, K
def feasible_new(Z, FP, FL):
    tP, tL = collections.defaultdict(list), collections.defaultdict(list)
    for i, (W, K) in enumerate(Z):
        for x in W: tP[x].append(i)
        for y in K: tL[y].append(i)
    if (FP & set(tP)) or (FL & set(tL)): return False
    cP = collections.Counter(tuple(v) for v in tP.values()); cL = collections.Counter(tuple(v) for v in tL.values())
    cP[()] = P - len(FP) - len(tP); cL[()] = P - len(FL) - len(tL)
    return cP == cL
def feasible_old(Z, FP, FL):
    seenP, seenL = set(), set()
    for W, K in Z:
        if W & seenP or K & seenL: return False
        seenP |= W; seenL |= K
    return not (FP & seenP) and not (FL & seenL) and len(FP) == len(FL) and not (FP & FL and False)
rng = random.Random(seed)
cands = []
for _ in range(ncand):
    p = rng.randrange(P); l = PL[p][rng.randrange(q + 1)]
    cands.append((p, l))
res = {}
for name, rule in (("OLD", feasible_old), ("NEW", feasible_new)):
    units, Z = [], []
    FP, FL = set(), set()
    for p, l in cands:
        if p in FP or l in FL: continue
        W, K = zones(p, l)
        if rule(Z + [(W, K)], FP | {p}, FL | {l}):
            units.append((p, l)); Z.append((W, K)); FP.add(p); FL.add(l)
    res[name] = len(units)
    print(f"{name}: accepted {len(units)} units of {ncand} random incident flags (seed {seed})")
# sanity: the NEW rule must accept every set the OLD rule accepts
print("sanity: NEW >= OLD:", res["NEW"] >= res["OLD"])
