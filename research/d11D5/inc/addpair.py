"""Add one more point-line pair to a DM base (plusopt format) by an incident switch (x* on l*, x* on dg-1 old lines,
l* through the dg-1 removed points and x*; kind a: dg flags, x* not on l*) on lines and points away from the earlier new
vertices; sigma(x*) = l*.  The nu file (one bit per flag, flag = l*dg + slot) is extended: switched flags keep their
slot and their bit, the new line's flags get 0.  usage: python3 addpair.py base.in nu.txt kind seed out.in out.nu"""
import sys, random
base, nuf, kind, seed, outb, outn = sys.argv[1:7]; rng = random.Random(int(seed))
t = open(base).read().split(); n, dg = int(t[0]), int(t[1])
ln = [[int(t[2 + l * dg + i]) for i in range(dg)] for l in range(n)]; sig = [int(x) for x in t[2 + n * dg:2 + n * dg + n]]
nu = open(nuf).read().split()
pl = [[] for _ in range(n)]
for l in range(n):
    for p in ln[l]: pl[p].append(l)
col = [set() for _ in range(n)]
for L in ln:
    for p in L: col[p].update(L)
lset = [set(L) for L in ln]
K = dg - 1 if kind == "b" else dg
# keep away from vertices within distance 2 of the inserted ones (ids >= 585 for W(8), i.e. n0 = first new id)
n0 = int(sys.argv[7]) if len(sys.argv) > 7 else 585
badP = set(range(n0, n)); badL = set(range(n0, n))
for l in range(n0, n): badP |= lset[l]
for p in range(n0, n): badL |= set(pl[p])
for p in list(badP): badL |= set(pl[p])
for l in list(badL): badP |= lset[l]
for _ in range(10000):
    Ls = []; cand = [l for l in range(n) if l not in badL]; rng.shuffle(cand)
    for l in cand:
        if all(not (lset[l] & lset[m]) for m in Ls): Ls.append(l)
        if len(Ls) == K: break
    ps = []
    for l in Ls:
        c = [p for p in ln[l] if p not in badP and all(p not in col[q] for q in ps)]
        if not c: break
        ps.append(rng.choice(c))
    if len(ps) == K and len(Ls) == K: break
X = n
for L, p in zip(Ls, ps): ln[L] = [X if q == p else q for q in ln[L]]
ln.append(list(ps) + ([X] if kind == "b" else []))
assert len(ln[-1]) == dg
sig.append(n)
with open(outb, "w") as f:
    f.write(f"{n + 1} {dg}\n")
    for L in ln: f.write(" ".join(map(str, L)) + "\n")
    for s in sig: f.write(f"{s}\n")
open(outn, "w").write("\n".join(nu + ["0"] * dg) + "\n")
print("added pair", n, "on lines", Ls, "points", ps)
