"""Export, for W(q) with the polarity/duality used by dcover.py, the opposite point pairs and the delta-orbit ids
of the 4 flags on each of their q+1 GQ 4-paths.  Binary file: int32 header (q, norb, npairs, npath, nflags),
then npairs*npath*4 int32 orbit ids, then nflags int32 orbit-of-flag, then nflags*2 int32 (point, line).
usage: python3 export_pairs.py q out.bin"""
import sys, struct
from dcover import load, flags_and_orbits, pt_lines
q, out = int(sys.argv[1]), sys.argv[2]
n, L, d_pt, d_ln, inv_ln = load(q)
fid, orb, norb = flags_and_orbits(n, L, d_pt, d_ln)
pl = pt_lines(n, L)
onL = [set(s) for s in L]
col = [set() for _ in range(n)]
for s in L:
    for a in s:
        col[a].update(s)
rows = []
np_ = 0
for P in range(n):
    for Q in range(P + 1, n):
        if Q in col[P]:
            continue
        np_ += 1
        for l1 in pl[P]:
            R = next(r for r in L[l1] if Q in col[r])
            m2 = next(m for m in pl[R] if Q in onL[m])
            rows += [orb[fid[(P, l1)]], orb[fid[(R, l1)]], orb[fid[(R, m2)]], orb[fid[(Q, m2)]]]
flags = sorted(fid.items(), key=lambda kv: kv[1])
with open(out, "wb") as f:
    f.write(struct.pack("5i", q, norb, np_, q + 1, len(fid)))
    f.write(struct.pack(f"{len(rows)}i", *rows))
    f.write(struct.pack(f"{len(fid)}i", *orb))
    f.write(struct.pack(f"{2*len(fid)}i", *[x for (p, l), _ in flags for x in (p, l)]))
print(f"q={q} norb={norb} pairs={np_} written {out}")
