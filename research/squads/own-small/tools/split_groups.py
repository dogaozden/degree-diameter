"""Split a gap_export_aut.g text file into per-group binary tables for flift (int32 N, then N*N uint16, identity 0)
and rep files ("N R rep..."). Usage: python3 split_groups.py t<N>.txt OUTDIR"""
import sys, os, numpy as np
fn, od = sys.argv[1], sys.argv[2]
os.makedirs(od, exist_ok=True)
f = open(fn)
while True:
    h = f.readline()
    if not h:
        break
    _, N, gid, R = h.split(); N, gid, R = int(N), int(gid), int(R)
    reps = f.readline().split()
    T = np.array([f.readline().split() for _ in range(N)], dtype=np.uint16)
    base = os.path.join(od, f"g{N}_{gid:04d}")
    with open(base + ".bin", "wb") as o:
        np.array([N], dtype=np.int32).tofile(o); T.tofile(o)
    abel = int((T == T.T).all())
    open(base + ".reps", "w").write(f"{N} {R} {' '.join(reps)}\n")
    open(base + ".info", "w").write(f"{N} {gid} abelian={abel}\n")
