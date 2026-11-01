# Orbit reps of Aut(Z101 x|_5 Z25) on G\{e}, then Stab(a)-orbit reps of b. Elements (a,j) -> id = a*25 + j.
import numpy as np, itertools, sys
P, K, R = 101, 25, 5
N = P * K
rp = [pow(R, j, P) for j in range(K)]
Sj = [sum(rp[:j]) % P for j in range(K)]          # S_j = 1 + r + ... + r^{j-1}
X = np.array([i // K for i in range(N)]); J = np.array([i % K for i in range(N)])
Sarr = np.array(Sj)
def mul(g, h):
    a1, j1 = g // K, g % K; a2, j2 = h // K, h % K
    return ((a1 + rp[j1] * a2) % P) * K + (j1 + j2) % K
# automorphisms phi_{u,t}(x,j) = (u x + t S_j, j)
auts = []
for u in range(1, P):
    for t in range(P):
        img = ((u * X + t * Sarr[J]) % P) * K + J
        auts.append(img)
auts = np.array(auts)               # 10100 x N
# verify homomorphism on random pairs for a few automorphisms
rng = np.random.default_rng(1)
MT = np.array([[mul(g, h) for h in range(N)] for g in range(0)]) if False else None
for trial in range(300):
    g, h = rng.integers(N), rng.integers(N)
    k = rng.integers(len(auts))
    img = auts[k]
    assert img[mul(g, h)] == mul(img[g], img[h]), "not a homomorphism"
assert len(set(auts[0].tolist())) == N
# orbits of G\{e} under Aut via union-find style labelling
orb = -np.ones(N, dtype=int)
reps = []
for g in range(1, N):
    if orb[g] >= 0: continue
    o = set(auts[:, g].tolist())
    for x in o: orb[x] = len(reps)
    reps.append(g)
print("Aut orbits on G\\{e}:", len(reps), "reps", reps, file=sys.stderr)
pairs = []
for a in reps:
    stab = auts[auts[:, a] == a]          # automorphisms fixing a
    seen = set([0, a]); bl = []
    for b in range(1, N):
        if b in seen: continue
        o = set(stab[:, b].tolist())
        seen |= o
        bl.append(min(o - {a}) if False else min(o))
    # keep only orbit members not equal to a or e (orbits of Stab on G\{e,a})
    bl = [b for b in bl if b != a and b != 0]
    pairs += [(a, b) for b in bl]
    print("a", a, "stab size", len(stab), "b-reps", len(bl), file=sys.stderr)
print("total (a,b) pairs", len(pairs), file=sys.stderr)
with open(sys.argv[1], "w") as f:
    f.write(f"{len(pairs)}\n")
    for a, b in pairs: f.write(f"{a} {b}\n")
