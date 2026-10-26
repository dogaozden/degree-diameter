import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r6-d11D5/c6")
from load import *
B = "/home/user/degree-diameter/research/d11D5/graphs/d11D5_n7044_k22.in"
n, L, sig = read(B)
mod = [l for l in range(n0) if sorted(L[l]) != sorted(LINES[l])]
flag = [d_ln[l] for l in mod]          # R with delta(R) = modified line
print("flagged R:", sorted(flag))
spans = {}
for i in range(len(flag)):
    for j in range(i+1, len(flag)):
        a, b = flag[i], flag[j]
        if not Bf(PTS[a], PTS[b]): continue
        h = span(PTS[a], PTS[b])
        k = frozenset(h & set(flag))
        if len(k) >= 7: spans[h] = k
for h, k in spans.items():
    print("hyperbolic line", sorted(h), "contains flagged", len(k), "delta-lines", sorted(d_pt[R] for R in k))
    print("  excluded R (unmodified):", sorted(set(h) - set(flag)), " their lines", sorted(d_pt[R] for R in set(h)-set(flag)))
    print("  is hyperbolic (Bf nonzero for some pair):", any(Bf(PTS[a], PTS[b]) for a in h for b in h if a < b))
