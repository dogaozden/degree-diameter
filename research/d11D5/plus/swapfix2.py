"""sigma = delta, then for each i: swap sigma(p_i) <-> sigma(y_i) (y_i in L_i \\ p_i) and
sigma(delta(L_i)) <-> sigma(delta(m_i)) (m_i a line through p_i, m_i != L_i).  usage: swapfix2.py p.json base.in seed out.in"""
import json, sys, random, os
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5"); here=os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n0, L0, d_pt, d_ln, inv = load(8); os.chdir(here)
d = json.load(open(sys.argv[1])); lines, pts = d["lines"], d["pts"]
f = open(sys.argv[2]); n, dg = map(int, f.readline().split())
Lb = [list(map(int, f.readline().split())) for _ in range(n)]
sig = [int(f.readline()) for _ in range(n)]
rng = random.Random(int(sys.argv[3]))
pos = {l: p for p, l in enumerate(sig)}
def swap(a, b):
    sig[a], sig[b] = sig[b], sig[a]; pos[sig[a]] = a; pos[sig[b]] = b
for li, p in zip(lines, pts):
    y = rng.choice([q for q in Lb[li] if q != 585]); swap(p, y)
    ms = [m for m in range(n0) if p in L0[m] and m != li]
    m = rng.choice(ms)
    swap(pos[li], pos[m])
with open(sys.argv[4], "w") as g:
    g.write(f"{n} {dg}\n")
    for s in Lb: g.write(" ".join(map(str, s)) + "\n")
    g.write("\n".join(map(str, sig)) + "\n")
