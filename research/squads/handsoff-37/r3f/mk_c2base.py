# mk_c2base.py NEARMISS_EDGES AUTS_JSON OUTSTATE: base for a FREE involution tau of the near miss (C2 lift, N = 2).
import json, sys
ef, aj, outp = sys.argv[1], sys.argv[2], sys.argv[3]
L = [l.split() for l in open(ef).read().strip().split('\n')]
n = int(L[0][0]); E = [(int(a), int(b)) for a, b in (x[:2] for x in L[1:])]
auts = json.load(open(aj)); m = n // 2
tau = next(p for p in auts if all(p[p[x]] == x for x in range(n)) and all(p[x] != x for x in range(n)))
seen = [False] * n; lab = [None] * n; reps = []
for x in range(n):
    if seen[x]: continue
    y = tau[x]; reps.append(x); seen[x] = True; lab[x] = (len(reps) - 1, 0)
    if y != x: seen[y] = True; lab[y] = (len(reps) - 1, 1)
Aorb = [i for i, r in enumerate(reps) if r < m]; Borb = [i for i, r in enumerate(reps) if r >= m]
aidx = {o: i for i, o in enumerate(Aorb)}; bidx = {o: i for i, o in enumerate(Borb)}
base = []
for x, y in E:
    if x >= m: x, y = y, x
    ou, g = lab[x]; ov, h = lab[y]
    if g != 0: continue
    base.append((aidx[ou], bidx[ov], (h - g) % 2))
k = len(Aorb); assert len(base) == 3 * k, (len(base), k)
open(outp, 'w').write(f"2 {k}\n" + "".join(f"{u} {v} {a}\n" for u, v, a in base))
print("k", k, "base edges", len(base))
