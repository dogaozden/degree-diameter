#!/usr/bin/env python3
# mk_variants.py BASE OUTDIR DT: test variants of one pgl solution (card B3 validation).
#   <stem>_D<DT>.txt     same generators, header D = DT (tight: must be VALID)
#   <stem>_D<DT-1>.txt   header D = DT-1 (must be INVALID: the diameter is DT)
#   <stem>_rep.txt       generator 3 repeated as generator 4 (both tools must reject)
#   <stem>_zc.txt        generator 2 with z -> z+1 mod n (verdict whatever the tools say; they must agree)
import os
import re
import sys

base, outdir, dt = sys.argv[1], sys.argv[2], int(sys.argv[3])
stem = os.path.splitext(os.path.basename(base))[0]
lines = [ln.rstrip("\n") for ln in open(base) if ln.strip()]
head = lines[0].split()
d = int(head[0])
gens = lines[1:1 + d]
n = int(head[head.index("n") + 1])


def write(name, hdr, gl):
    with open(os.path.join(outdir, name), "w") as f:
        f.write(hdr + "\n" + "\n".join(gl) + "\n")


def with_D(D):
    h = head[:]
    h[1] = str(D)
    return " ".join(h)


write(f"{stem}_D{dt}.txt", with_D(dt), gens)
write(f"{stem}_D{dt - 1}.txt", with_D(dt - 1), gens)
g4 = gens[:3] + [gens[2]] + gens[3:]
write(f"{stem}_rep.txt", with_D(dt), g4[:d])
m = re.fullmatch(r"(\S+) mat\(([^)]*)\) z=(\d+)", gens[1])
zc = gens[:1] + [f"{m.group(1)} mat({m.group(2)}) z={(int(m.group(3)) + 1) % n}"] + gens[2:]
write(f"{stem}_zc.txt", with_D(dt), zc)
print("variants of", stem, "written with D =", dt)
