# mk_c3base.py NEARMISS_EDGES AUTS_JSON OUTSTATE: lift base for a free order-3 automorphism tau of the near miss.
# state format (lift3 INIT): "N k" then "u v a" per base edge; lift vertex (u,g) = u*N+g (A), (k+v,g) = (k+v)*N+g (B)
import json, sys
ef, aj, outp = sys.argv[1], sys.argv[2], sys.argv[3]
L = [l.split() for l in open(ef).read().strip().split('\n')]
n = int(L[0][0]); E = [(int(a), int(b)) for a, b in (x[:2] for x in L[1:])]
auts = json.load(open(aj))
n_ = n
def is_free_o3(p):
    return all(p[p[p[x]]] == x for x in range(n)) and all(p[x] != x for x in range(n)) and any(p[x] != x for x in range(n))
tau = None
for p in auts:
    if is_free_o3(p):
        tau = p; break
assert tau is not None, "no free order-3 element"
m = n // 2
# orbits and labels: lab[x] = (orbit index, g) with x = tau^g(rep)
seen = [False] * n; lab = [None] * n; reps = []
for x in range(n):
    if seen[x]: continue
    orb = [x]; y = tau[x]
    while y != x: orb.append(y); y = tau[y]
    for g in range(3): seen[orb[g]] = True
    reps.append(x)
    for g, z in enumerate(orb): lab[z] = (len(reps) - 1, g)
# orbit ids: A orbits are those with rep < m (A side), B orbits the rest
Aorb = [i for i, r in enumerate(reps) if r < m]; Borb = [i for i, r in enumerate(reps) if r >= m]
assert len(Aorb) == len(Borb) == m // 3, (len(Aorb), len(Borb))
aidx = {o: i for i, o in enumerate(Aorb)}; bidx = {o: i for i, o in enumerate(Borb)}
k = len(Aorb)
base = []
for x, y in E:
    if x >= m: x, y = y, x
    ou, g = lab[x]; ov, h = lab[y]
    if g != 0: continue  # one base edge per edge orbit: keep the edges at orbit representatives
    assert ou in aidx and ov in bidx
    base.append((aidx[ou], bidx[ov], (h - g) % 3))
assert len(base) == 3 * k
with open(outp, 'w') as f:
    f.write(f"3 {k}\n")
    for u, v, a in base: f.write(f"{u} {v} {a}\n")
print("k", k, "base edges", len(base), "tau fixed pts", sum(1 for x in range(n) if tau[x] == x))
