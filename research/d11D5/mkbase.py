"""Base multigraph for a Z2-extension lift: W(q) incidence graph + two parallel copies of a duality matching
P -> delta(P) (delta = Klein duality o Frobenius^m from w{q}.json; a polarity when m = polarity_m).
Group G = Z_K x Z2 (mode 0) or Z_2K with N = {0, K} (mode 1).  Every edge carries a fixed element of G and,
optionally, a free Z2 variable added in N.  GQ flags: fixed 0, variable = flag index.  Jump copies a = 1, 2:
fixed J_a (given), variable eps(P) (tie: one per point for both copies), eps_a(P) (untie) or none.
Output format (zcons.c): "V nvars mode K" then edges "u v fixed var" (voltage u -> v; var = -1 for none).
usage: python3 mkbase.py q m mode K J1 J2 eps(tie|untie|none) out.txt"""
import sys, json
q, m, mode, K, J1, J2, eps, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7], sys.argv[8]
W = json.load(open(f"w{q}.json"))
n = len(W["points"]); L = W["lines"]
def pw(perm, k):
    r = list(range(n))
    for _ in range(k):
        r = [perm[x] for x in r]
    return r
fpm, flm = pw(W["frob_pt"], m), pw(W["frob_ln"], m)
d_pt = [W["klein_pt"][fpm[x]] for x in range(n)]
d_ln = [W["klein_ln"][flm[x]] for x in range(n)]
assert all(d_ln[li] in L[d_pt[pi]] for li in range(n) for pi in L[li]), "not a duality"
pol = all(d_ln[d_pt[x]] == x for x in range(n))
edges = []
nf = 0
for li in range(n):
    for p in L[li]:
        edges.append((p, n + li, 0, nf)); nf += 1
nv = nf
for a, J in ((1, J1), (2, J2)):
    for p in range(n):
        if eps == "tie":
            var = nf + p
        elif eps == "untie":
            var = nf + (a - 1) * n + p
        else:
            var = -1
        edges.append((p, n + d_pt[p], J, var))
nv = nf + (n if eps == "tie" else 2 * n if eps == "untie" else 0)
with open(out, "w") as f:
    f.write(f"{2*n} {nv} {mode} {K}\n")
    for e in edges:
        f.write("%d %d %d %d\n" % e)
absol = sum(1 for p in range(n) if p in L[d_pt[p]])
print(f"W({q}) m={m} polarity={pol} absolute points={absol} V={2*n} edges={len(edges)} vars={nv} -> {out}")
