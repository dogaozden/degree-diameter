"""Local sigma block for po7 BLOCKS: Loc = new points, points of new lines, points of switched lines, sigma^-1 of new
lines, switched lines and lines through moved points (radius r=1), optionally widened by collinearity (r=2).
usage: mkblk.py base.in out.blk [r]   (old lines = ids < 585 that differ from W(8) are 'switched')"""
import sys
sys.argv += [] 
from gq import LINES, n0
base, out = sys.argv[1], sys.argv[2]; r = int(sys.argv[3]) if len(sys.argv) > 3 else 1
t = open(base).read().split(); n, dg = int(t[0]), int(t[1])
ln = [[int(x) for x in t[2+l*dg:2+l*dg+dg]] for l in range(n)]; sig = [int(x) for x in t[2+n*dg:2+n*dg+n]]
sinv = [0]*n
for p, l in enumerate(sig): sinv[l] = p
pl = [[] for _ in range(n)]
for l in range(n):
    for p in ln[l]: pl[p].append(l)
sw = [l for l in range(n0) if sorted(ln[l]) != sorted(LINES[l])] + list(range(n0, n))
loc = set(range(n0, n))
for l in sw: loc.update(ln[l])
moved = set(p for l in range(n0, n) for p in ln[l])
L1 = set(sw)
for p in moved: L1.update(pl[p])
for x in range(n0, n): L1.update(pl[x])
loc.update(sinv[l] for l in L1)
if r >= 2:
    extra = set()
    for p in list(loc):
        for l in pl[p]: extra.update(ln[l])
    loc |= extra
loc = sorted(loc); rest = [p for p in range(n) if p not in set(loc)]
with open(out, "w") as f:
    f.write(f"{len(loc)} " + " ".join(map(str, loc)) + "\n")
    if rest:
        f.write(f"{len(rest)} " + " ".join(map(str, rest)) + "\n")
        f.write(f"{len(rest)} " + " ".join(map(str, rest)) + "\n")
print("local points", len(loc), file=sys.stderr)
