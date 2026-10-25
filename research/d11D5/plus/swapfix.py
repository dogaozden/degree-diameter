"""Structured sigma for the spread switch: sigma = delta, then for each i swap sigma(p_i) <-> sigma(y_i), y_i in L_i \\ p_i.
usage: python3 swapfix.py p.txt.json base.in seed out.in"""
import json, sys, random
d = json.load(open(sys.argv[1])); lines, pts = d["lines"], d["pts"]
f = open(sys.argv[2]); n, dg = map(int, f.readline().split())
Lb = [list(map(int, f.readline().split())) for _ in range(n)]
sig = [int(f.readline()) for _ in range(n)]
rng = random.Random(int(sys.argv[3]))
for li, p in zip(lines, pts):
    ys = [q for q in Lb[li] if q != 585]
    y = rng.choice(ys)
    sig[p], sig[y] = sig[y], sig[p]
with open(sys.argv[4], "w") as g:
    g.write(f"{n} {dg}\n")
    for s in Lb: g.write(" ".join(map(str, s)) + "\n")
    g.write("\n".join(map(str, sig)) + "\n")
