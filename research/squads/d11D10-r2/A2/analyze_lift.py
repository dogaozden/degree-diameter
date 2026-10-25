# Lift DUMP analysis: degenerate (cost >= THR) vs order of the orbit generator x (Q-part)
import sys, re, collections
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d11D10-r2/A2")
import analyze, gf
from gf import mmul, pnorm
I = (1, 0, 0, 1)
def mp(X, e):
    R = I; B = X
    while e:
        if e & 1: R = mmul(R, B)
        B = mmul(B, B); e >>= 1
    return R
def pm1(M):
    return M[1] == 0 and M[2] == 0 and M[0] == M[3] and M[0] in (1, gf.NEG[1])
def ord122(X):
    return pm1(mp(X, 122)) and not pm1(mp(X, 61)) and not pm1(mp(X, 2))
path = sys.argv[1]
thr = int(sys.argv[2]) if len(sys.argv) > 2 else 10**6
rows = analyze.parse(path)
hist = {}
for line in open(path):
    m = re.match(r"HISTB (.*) sum (\d+)", line)
    if m: hist.setdefault("B", []).append(line.strip())
    m = re.match(r"HISTA (.*) sum (\d+)", line)
    if m: hist.setdefault("A", []).append(line.strip())
print("samples", len(rows), "cost values:", sorted(collections.Counter(r[1] for r in rows).items())[:10])
tab = collections.Counter()
for t, cost, orbit in rows:
    x = orbit[0][0]
    deg = cost >= thr
    o122 = ord122(x)
    o = gf.pow_order(x)
    tab[("deg" if deg else "ok", "ord=%s" % o)] += 1
print(sorted(tab.items()))
print("order122 vs degenerate:", collections.Counter((ord122(r[2][0][0]), r[1] >= thr) for r in rows))
for k in hist:
    print(hist[k][:2])
