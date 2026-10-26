import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r6-d11D5/c6")
from load import *
B = "/home/user/degree-diameter/research/d11D5/graphs/d11D5_n7044_k22.in"
n, L, sig = read(B)
print("n", n, "n0", n0, "lines in W8", len(LINES))
diff = [l for l in range(n0) if sorted(L[l]) != sorted(LINES[l])]
print("old lines (0..584) differing from W(8):", len(diff), diff)
for l in diff:
    print(" line", l, "W8-only points", sorted(set(LINES[l]) - set(L[l])), "base-only", sorted(set(L[l]) - set(LINES[l])))
# point degrees
deg = [0]*n
for l in L:
    for p in l: deg[p] += 1
print("point degrees", set(deg), "line sizes", set(len(l) for l in L))
# sigma bijection
print("sigma bijection", sorted(sig) == list(range(n)))
# sigma vs delta: d_pt
same = sum(1 for p in range(n0) if sig[p] == d_pt[p])
print("sigma(p) == d_pt[p] count (old points):", same)
# which line-ids are "delta(R)" for R: W8 line index of R's polar
print("d_pt[0..5]", [d_pt[i] for i in range(6)])
