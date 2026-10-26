# Writes the component packing instance for W(9): singles (weight 1) and non-S collinear pairs (weight 2).
# Format: first line "nlines ncomps"; then per component: "w m l_1..l_m k p_1..p_k"
# (m = number of lines used, l_i = line ids; k = number of points, p_i = point ids).
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W
G = W(9)
S = set(regular_spread_W(G))
out = []
for p in range(G.np):
    out.append((1, list(G.plines[p]), [p]))
for p in range(G.np):
    for r in range(p + 1, G.np):
        if G.col[p, r]:
            L = [L for L in G.plines[p] if r in G.lines[L]][0]
            if L in S:
                continue
            lines = sorted(set(G.plines[p]) | set(G.plines[r]))
            out.append((2, lines, [p, r]))
with open('comps_W9.txt', 'w') as f:
    f.write(f"{len(G.lines)} {len(out)}\n")
    for w, lines, pts in out:
        f.write(f"{w} {len(lines)} " + " ".join(map(str, lines)) + f" {len(pts)} " + " ".join(map(str, pts)) + "\n")
print("lines", len(G.lines), "comps", len(out), "pairs", sum(1 for o in out if o[0] == 2), "S", len(S))
