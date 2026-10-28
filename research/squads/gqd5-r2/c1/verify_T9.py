# Recomputes the relaxed-set conditions for a candidate T of W(9): every point of T has <= 1 collinear neighbour in T,
# and no pair of T is joined by a line of S. Usage: verify_T9.py best_T9.json
import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W
G = W(9)
S = set(regular_spread_W(G))
T = sorted(json.load(open(sys.argv[1])))
assert len(set(T)) == len(T), "duplicates"
Ts = set(T)
ok = True
for p in T:
    nbrs = [r for L in G.plines[p] for r in G.lines[L] if r != p and r in Ts]
    if len(nbrs) > 1:
        ok = False; print("point", p, "has T-neighbours", nbrs)
for p in T:
    for q2 in T:
        if p < q2 and G.col[p, q2]:
            L = [L for L in G.plines[p] if q2 in G.lines[L]][0]
            if L in S:
                ok = False; print("forbidden pair", p, q2, "on spread line", L)
print("VALID" if ok else "INVALID", "size", len(T))
