# Independent check of a flag packing in GH(q) (c1 card): reads the hexagon file (format "P q", then one line of
# q+1 point ids per line), recomputes the zones of each flag (p,l) from the definitions and checks that every flag is
# incident and that all point zones and all line zones are pairwise disjoint.
# Usage: python3 -I verify_packing.py GHFILE FLAGS
import sys
gh, flagsf = sys.argv[1], sys.argv[2]
with open(gh) as f:
    P, q = map(int, f.readline().split())
    Q1 = q + 1
    LP = []
    for _ in range(P):
        LP.append(list(map(int, f.readline().split())))
assert all(len(r) == Q1 for r in LP)
PL = [[] for _ in range(P)]
for l, pts in enumerate(LP):
    for p in pts:
        PL[p].append(l)
assert all(len(x) == Q1 for x in PL)
flags = []
with open(flagsf) as f:
    for line in f:
        s = line.split()
        if len(s) == 2:
            flags.append((int(s[0]), int(s[1])))
bad_inc = sum(1 for p, l in flags if l not in PL[p])
ps = [p for p, _ in flags]
dup_p = len(ps) - len(set(ps))
owner_p, owner_l = {}, {}
overlaps = 0
for i, (p, l) in enumerate(flags):
    zp = {p}
    for L in PL[p]:
        if L != l:
            zp.update(w for w in LP[L] if w != p)
    zl = {l}
    for x in LP[l]:
        if x != p:
            zl.update(K for K in PL[x] if K != l)
    for e in zp:
        if e in owner_p:
            overlaps += 1
        else:
            owner_p[e] = i
    for e in zl:
        if e in owner_l:
            overlaps += 1
        else:
            owner_l[e] = i
ok = bad_inc == 0 and dup_p == 0 and overlaps == 0
print(("VALID" if ok else "INVALID"), len(flags), "flags; non-incident", bad_inc, "duplicate points", dup_p,
      "zone collisions", overlaps, "zone sizes", len(zp), len(zl))
