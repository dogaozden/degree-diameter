"""conv.py TXT OUTDIR: split a 'G N id name' + N rows text table file into per-group .bin (int32 N, uint16 N*N)."""
import sys, os, numpy as np
fn, od = sys.argv[1], sys.argv[2]
os.makedirs(od, exist_ok=True)
lines = open(fn).read().split("\n")
i = 0; out = []
while i < len(lines):
    h = lines[i].split()
    if not h or h[0] != "G":
        i += 1; continue
    N, gid = int(h[1]), int(h[2])
    rows = [list(map(int, lines[i + 1 + r].split())) for r in range(N)]
    T = np.array(rows, dtype=np.uint16)
    p = os.path.join(od, f"g{N}_{gid:02d}.bin")
    with open(p, "wb") as o:
        np.array([N], dtype=np.int32).tofile(o); T.tofile(o)
    out.append(p)
    i += 1 + N
print(len(out), "groups")
