"""For the newest pair (point n-1, line n-1) of a base: make sigma(points of l*) the pencil of an old point c (sigma
swaps), and optionally sigma^-1(lines of x*) the points of an old line m.  Tries several c (and m), keeps the best po7 score.
usage: python3 pencil.py in.in out.in [tries]"""
import sys, subprocess, os, random
src, out = sys.argv[1], sys.argv[2]; tries = int(sys.argv[3]) if len(sys.argv) > 3 else 30
t = open(src).read().split(); n, dg = int(t[0]), int(t[1])
ln = [[int(t[2 + l * dg + i]) for i in range(dg)] for l in range(n)]; sig0 = [int(x) for x in t[2 + n * dg:2 + n * dg + n]]
pl = [[l for l in range(n) if p in ln[l]] for p in range(n)]
def write(fn, s):
    with open(fn, "w") as f:
        f.write(f"{n} {dg}\n")
        for L in ln: f.write(" ".join(map(str, L)) + "\n")
        for v in s: f.write(f"{v}\n")
def score(s):
    write("/tmp/pc.in", s)
    o = subprocess.run(["/tmp/po7", "/tmp/pc.in"], env={**os.environ, "SCORE": "1"}, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])
X = n - 1; Lstar = n - 1
rng = random.Random(1)
best = (score(sig0), sig0); print("start", best[0])
near = set(ln[Lstar]) | {X}
for _ in range(tries):
    c = rng.randrange(n - 1)
    if c in near: continue
    s = sig0[:]; pos = {v: i for i, v in enumerate(s)}
    for p, lam in zip(ln[Lstar], pl[c]):
        a, b = p, pos[lam]; s[a], s[b] = s[b], s[a]; pos[s[a]] = a; pos[s[b]] = b
    sc = score(s)
    if sc < best[0]: best = (sc, s); print("c", c, "->", sc)
write(out, best[1]); print("best", best[0])
