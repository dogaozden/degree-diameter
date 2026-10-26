"""Coordinate descent with full single-generator scans (lift eval), then a restricted pair scan.
Usage: python3 descend.py G.bin TOOLS_DIR SOLFILE[,SOLFILE...] PAIR_TOPK
S = [0, x, y, z] (s0 = e fixed by the isomorphism S -> cS). Cost = lift eval cost (invalid = large)."""
import sys, subprocess, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hard import load_table, read_S, inverses, far_sets

G, TOOLS = sys.argv[1], sys.argv[2]
files = sys.argv[3].split(",")
TOPK = int(sys.argv[4])
LIFT = os.path.join(TOOLS, "lift")
BASE = os.path.join(TOOLS, "bases", "dipole4.txt")
N, T = load_table(G)
BIG = 10 ** 9

def run(lines):
    if not lines:
        return []
    inp = "\n".join(" ".join(map(str, s)) for s in lines) + "\n"
    out = subprocess.run([LIFT, BASE, G, "4", "8", "eval"], input=inp, capture_output=True, text=True,
                         env=dict(os.environ, THREADS="1")).stdout.split()
    return [BIG if t == "invalid" else int(t) for t in out]

def scan(S, i):
    cands = [g for g in range(1, N) if g not in S]
    lines = []
    for g in cands:
        S2 = list(S); S2[i] = g; lines.append(S2)
    c = run(lines)
    return cands, c

def cost(S):
    return run([S])[0]

random.seed(int(os.environ.get("SEED", "1")))
best_overall = (BIG, None)
for f in files:
    S = read_S(f)
    c = cost(S)
    improved = True
    rounds = 0
    while improved and rounds < 6:
        improved = False
        rounds += 1
        for i in (1, 2, 3):
            cands, cs = scan(S, i)
            m = min(cs)
            if m < c:
                ties = [g for g, v in zip(cands, cs) if v == m]
                S[i] = random.choice(ties); c = m; improved = True
    print(os.path.basename(f), "descent cost", c, "S", S, "rounds", rounds, flush=True)
    if c < best_overall[0]:
        best_overall = (c, list(S))

c0, S = best_overall
print("best after descent", c0, S, flush=True)
# restricted pair scan: fix x = S[1], take the top-K values for y = S[2] from its single scan, all z = S[3]
cands, cs = scan(S, 2)
order = sorted(zip(cs, cands))[:TOPK]
ys = [g for _, g in order if g != S[1]]
lines = []
for y in ys:
    for z in range(1, N):
        if z in (S[1], y):
            continue
        lines.append([0, S[1], y, z])
cs2 = run(lines)
best = min(zip(cs2, lines), key=lambda t: t[0])
print("pair scan: lines", len(lines), "best", best[0], best[1], flush=True)
if best[0] < c0:
    S = best[1]; c0 = best[0]
fa, fb = far_sets(N, T, inverses(N, T), S)
print("FINAL cost", c0, "S", S, "far from A", len(fa), "far from B", len(fb), flush=True)
print("uncovered B-side elements (src A):", sorted(g for side, g in fa if side == "B"))
print("uncovered A-side elements (src A):", sorted(g for side, g in fa if side == "A"))
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "best_%s.sol" % os.path.basename(G)), "w") as f:
    f.write("e 0 1 0\n" + "".join("e 0 1 %d\n" % s for s in S[1:]))
