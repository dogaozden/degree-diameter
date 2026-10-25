"""Convert a haar_gen / haar_sym solution file (header "d D sl|psl p n ...", then lines "<idx> mat(a,b,c,d) z=Z")
into a bcd lift spec: the Haar graph H(G,S), G = (P)SL(2,p) x Z_n, is the lift of the dipole (base vertices 0 = A,
1 = B, one base edge per s in S) with (A, g) ~ (B, s g).  Only prime p (sl/psl families).
Usage: python3 haar2lift.py SOL.txt OUT.spec"""
import re
import sys

src, out = sys.argv[1], sys.argv[2]
lines = open(src).read().splitlines()
h = lines[0].split()
d, D, fam, p = int(h[0]), int(h[1]), h[2], int(h[3])
assert fam in ("sl", "psl"), "only sl/psl families"
n = int(h[h.index("n") + 1])
S = []
for ln in lines[1:]:
    m = re.search(r"mat\((\d+),(\d+),(\d+),(\d+)\)", ln); z = re.search(r"z=(\d+)", ln)
    if m and z:
        S.append(tuple(map(int, m.groups())) + (int(z.group(1)),))
assert len(S) == d, (len(S), d)
with open(out, "w") as f:
    f.write(f"bcd-lift 1\ngroup {fam} {p} {n}\nvertices 2\nedges {d}\n")
    for s in S:
        f.write("0 1 %d %d %d %d %d\n" % s)
    f.write("end\n")
print(f"{src}: d={d} D={D} {fam}({p}) x Z_{n} -> {out}")
