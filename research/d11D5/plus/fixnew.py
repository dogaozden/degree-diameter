"""Targeted swaps for the fibres of x* and l*: (a) make sigma^-1(L_i) a point on some switch line;
(b) make sigma(p_m) a line through some p_j.  Scores each single swap with plusopt2 (via a temp file), greedy."""
import sys, subprocess, json, itertools
base = sys.argv[1]; meta = json.load(open(sys.argv[2])); out = sys.argv[3]
def rd(fn):
    f = open(fn); n, dg = map(int, f.readline().split())
    L = [list(map(int, f.readline().split())) for _ in range(n)]
    sig = [int(f.readline()) for _ in range(n)]
    return n, dg, L, sig
def wr(fn, n, dg, L, sig):
    with open(fn, "w") as g:
        g.write(f"{n} {dg}\n"); [g.write(" ".join(map(str, s)) + "\n") for s in L]; g.write("\n".join(map(str, sig)) + "\n")
def score(fn):
    o = subprocess.run(["./plusopt2", fn], env={"SCORE": "1"}, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])
n, dg, L, sig = rd(base); X = n - 1; LS = n - 1
pos = {l: p for p, l in enumerate(sig)}
def trial(a, b):
    s2 = sig[:]; s2[a], s2[b] = s2[b], s2[a]; wr("/tmp/fx.in", n, dg, L, s2); return score("/tmp/fx.in"), s2
best = score(base); print("start", best)
sw = [l for l in range(n) if X in L[l]]          # switch lines (contain x*)
on_sw = sorted(set(p for l in sw for p in L[l] if p != X))
cand = []
for li in sw:
    for z in on_sw:
        cand.append((z, pos[li]))
pj = L[LS]
for pm in pj:
    for p in pj:
        for l in range(n):
            if p in L[l] and l != LS: cand.append((pm, pos[l]))
print("candidates", len(cand))
res = []
for a, b in cand:
    if a == b: continue
    c, s2 = trial(a, b); res.append((c, a, b))
res.sort(); print("best single swaps", res[:6])
c, a, b = res[0]
if c < best:
    sig[a], sig[b] = sig[b], sig[a]; wr(out, n, dg, L, sig); print("wrote", out, c)
