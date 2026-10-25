"""k point-line insertions into a GQ base with a random-like sigma (plusopt format), each an incident switch (kind b:
x_j* on l_j*, on K = dg-1 old lines; l_j* through the K removed points and x_j*) or a plain switch (kind a: K = dg),
on disjoint old lines and points; sigma(x_j*) = l_j*.  Scores each start with ./po7 and keeps the best.
usage: python3 genk.py base.in kind k N seed outprefix"""
import random, subprocess, sys, os, json
base, kind, k, N, seed, outp = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
t = open(base).read().split(); n, dg = int(t[0]), int(t[1])
ln = [[int(t[2 + l * dg + i]) for i in range(dg)] for l in range(n)]; sig = [int(x) for x in t[2 + n * dg:2 + n * dg + n]]
col = [set() for _ in range(n)]
for L in ln:
    for p in L: col[p].update(L)
lset = [set(L) for L in ln]
rng = random.Random(seed)
K = dg - 1 if kind == "b" else dg
def one(usedL, usedP):
    for _ in range(1000):
        Ls = []; cand = [l for l in range(n) if l not in usedL]; rng.shuffle(cand)
        for l in cand:
            if all(not (lset[l] & lset[m]) for m in Ls): Ls.append(l)
            if len(Ls) == K: break
        ps = []
        for l in Ls:
            c = [p for p in ln[l] if p not in usedP and all(p not in col[q] for q in ps)]
            if not c: break
            ps.append(rng.choice(c))
        if len(ps) == K: return Ls, ps
    return None
res = []
for it in range(N):
    usedL, usedP = set(), set(); sw = []
    for j in range(k):
        r = one(usedL, usedP)
        if r is None: break
        sw.append(r); usedL |= set(r[0]); usedP |= set(r[1])
    if len(sw) < k: continue
    ln2 = [list(L) for L in ln] + [None] * k; sig2 = list(sig) + [None] * k
    for j, (Ls, ps) in enumerate(sw):
        X = n + j
        for L, p in zip(Ls, ps): ln2[L] = [X if q == p else q for q in ln2[L]]
        ln2[n + j] = list(ps) + ([X] if kind == "b" else [])
        sig2[n + j] = n + j
    fn = f"{outp}_{it}.in"
    with open(fn, "w") as f:
        f.write(f"{n + k} {dg}\n")
        for L in ln2: f.write(" ".join(map(str, L)) + "\n")
        for s in sig2: f.write(f"{s}\n")
    out = subprocess.run(["./po7", fn], env={**os.environ, "SCORE": "1"}, capture_output=True, text=True).stdout
    c = int(out.split("cost=")[1].split()[0]); res.append((c, fn))
res.sort()
for c, fn in res[3:]: os.remove(fn)
print(kind, "k", k, "best", res[:3], "median", res[len(res) // 2][0])
