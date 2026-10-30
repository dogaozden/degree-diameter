#!/usr/bin/env python3
"""canon_eq.py A.edges B.edges ...: are these edge lists isomorphic graphs?  (nauty-labelg canonical forms)"""
import sys, subprocess, tempfile, os
import numpy as np
def g6(nv, edges):
    bits = np.zeros((nv * (nv - 1)) // 2 + 6, dtype=np.uint8)
    e = np.array(edges, dtype=np.int64); a = np.minimum(e[:, 0], e[:, 1]); b = np.maximum(e[:, 0], e[:, 1])
    bits[b * (b - 1) // 2 + a] = 1
    L = ((nv * (nv - 1)) // 2 + 5) // 6
    v = bits[:6 * L].reshape(L, 6) @ np.array([32, 16, 8, 4, 2, 1], dtype=np.uint8) + 63
    return chr(126) + chr(63 + ((nv >> 12) & 63)) + chr(63 + ((nv >> 6) & 63)) + chr(63 + (nv & 63)) + v.astype(np.uint8).tobytes().decode()
forms = []
with tempfile.TemporaryDirectory() as d:
    for p in sys.argv[1:]:
        t = open(p).read().split(); nv = int(t[0]); e = list(zip(map(int, t[1::2]), map(int, t[2::2])))
        open(os.path.join(d, "a.g6"), "w").write(g6(nv, e) + "\n")
        subprocess.run(["nauty-labelg", "-q", os.path.join(d, "a.g6"), os.path.join(d, "b.g6")], check=True)
        forms.append(open(os.path.join(d, "b.g6")).read().strip())
        print(f"{p}: {nv} vertices, {len(e)} edges")
print("ISOMORPHIC" if len(set(forms)) == 1 else "NOT ISOMORPHIC")
