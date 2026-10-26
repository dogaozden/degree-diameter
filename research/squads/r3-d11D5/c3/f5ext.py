"""Add a second pair to the cost-2 one-pair state best_f5.in (n = 586 -> 587).  Incident absolute switch for x2 = 586, l2 = 586
(absolute points of the polarity, 8 flags), then two sigma options:
  A: sigma(x2) = l2 (keeps the old sigma);  B: sigma(x2) = l* (585) and sigma(q) = l2, q = sigma^-1(585).
usage: python3 f5ext.py seed"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
spec = __import__("importlib.util").util.spec_from_file_location("gen", os.path.join(HERE, "gen.py"))
gen = __import__("importlib.util").util.module_from_spec(spec); spec.loader.exec_module(gen)
src = "/home/user/degree-diameter/research/d11D5/plus/best_f5.in"
tok = open(src).read().split()
n, dg = int(tok[0]), int(tok[1]); assert n == 586 and dg == 9
vals = list(map(int, tok[2:]))
Lsets = [set(vals[9 * l: 9 * l + 9]) for l in range(n)] + [set()]
sig = vals[9 * n: 9 * n + n]
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
s = None
for _ in range(500):
    s = gen.sample(Lsets, rng, 8, "absolute", [], [], False, False)
    if s: break
lines, pts = s
gen.apply(Lsets, 586, 586, lines, pts, True)
Ls = [sorted(x) for x in Lsets]
deg = [0] * 587
for x in Ls:
    assert len(x) == 9
    for p in x: deg[p] += 1
assert all(d == 9 for d in deg), "points"
sA = sig + [586]
q = sig.index(585)
sB = sig[:] + [585]; sB[q] = 586
for name, sg in (("A", sA), ("B", sB)):
    assert sorted(sg) == list(range(587))
    gen.write(os.path.join(HERE, "runs", f"f5ext{name}.in"), Ls, sg)
print("lines", lines, "pts", pts)
