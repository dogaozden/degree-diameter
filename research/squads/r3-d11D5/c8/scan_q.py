"""c8: for a switch (mode, seed), try every sigma(x*) <-> sigma(q) swap (q = any old point) and score with po7."""
import sys, subprocess, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r3-d11D5/c8")
from mkswitch import switch, write
C8 = "/home/user/degree-diameter/research/squads/r3-d11D5/c8"
PO7 = C8 + "/po7"
res = []
for mode, seed in [(a.split(":")[0], int(a.split(":")[1])) for a in sys.argv[1:]]:
    NP, Lnew, sigma0, pts, lines = switch(mode, seed)
    n = NP - 1
    fn = f"{C8}/work/scan_{mode}{seed}.in"
    best = None
    for q in range(n):
        sigma = sigma0[:]
        sigma[n] = sigma0[q]; sigma[q] = n
        write(fn, NP, Lnew, sigma)
        out = subprocess.run([PO7, fn], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
        c = int(out.strip().split("cost=")[1].split()[0])
        res.append((c, mode, seed, q))
        if best is None or c < best[0]:
            best = (c, q)
    print(mode, seed, "best q", best, "pts", pts, flush=True)
res.sort()
print("overall top 10:", res[:10])
import collections
print("hist of costs (count<=200):", sorted(collections.Counter(c for c, *_ in res if c <= 400).items())[:30])
