"""Greedy sigma for the newest pair: try every swap sigma(x*) <-> sigma(u) (u any point), keep the best (po7 score),
then every swap of the preimage of l*.  usage: python3 greedynew.py in.in out.in"""
import sys, subprocess, os
src, out = sys.argv[1], sys.argv[2]
t = open(src).read().split(); n, dg = int(t[0]), int(t[1])
head = t[:2 + n * dg]; sig = [int(x) for x in t[2 + n * dg:2 + n * dg + n]]
def write(fn, s):
    with open(fn, "w") as f:
        f.write(f"{n} {dg}\n")
        for l in range(n): f.write(" ".join(head[2 + l * dg:2 + (l + 1) * dg]) + "\n")
        for v in s: f.write(f"{v}\n")
def score(s):
    write("/tmp/gn.in", s)
    o = subprocess.run(["/tmp/po7", "/tmp/gn.in"], env={**os.environ, "SCORE": "1"}, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])
X = n - 1; best = score(sig); print("start", best)
for which in ("x", "l"):
    a = X if which == "x" else sig.index(X)
    cands = []
    for u in range(n):
        if u == a: continue
        s2 = sig[:]; s2[a], s2[u] = s2[u], s2[a]; c = score(s2); cands.append((c, u))
    cands.sort(); c, u = cands[0]
    if c < best: sig[a], sig[u] = sig[u], sig[a]; best = c
    print(which, "best swap", u, "->", best)
write(out, sig)
