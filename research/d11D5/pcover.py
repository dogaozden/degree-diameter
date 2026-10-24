"""Polarity cover of W(q), q = 2^(2e+1): base = W(q) + j parallel copies of the polarity matching P -> delta(P),
with voltages 1..j, lifted by Z_M, M = 2j+2, GQ voltages phi in {0, M/2} (delta-invariant, from orbit bits).
Max degree q+1+j, 2*M*(q+1)(q^2+1) vertices.
usage: python3 pcover.py q j phi.json out.txt"""
import sys, json
from dcover import load, flags_and_orbits
q, j, phif, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
M = 2 * j + 2
n, L, d_pt, d_ln, inv_ln = load(q)
assert all(inv_ln[p] == d_pt[p] for p in range(n)), "delta is not a polarity"
fid, orb, norb = flags_and_orbits(n, L, d_pt, d_ln)
bits = json.load(open(phif))["orbit_bits"]
with open(out, "w") as fo:
    fo.write(f"{n} {n} {M}\n")
    for (p, li), f in fid.items():
        fo.write(f"{p} {li} {(M // 2) * bits[orb[f]]}\n")
    for p in range(n):
        for t in range(1, j + 1):
            fo.write(f"{p} {d_pt[p]} {t}\n")
print(f"q={q} j={j} M={M} vertices={2*M*n} maxdeg={q+1+j}")
