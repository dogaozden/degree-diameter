#!/usr/bin/env python3
# i16: write group tables (int32 N, then N*N uint16, T[s*N+g] = s*g) for exh3, built with research/d5/groups.py
import sys, struct
sys.path.insert(0, "/home/user/degree-diameter/research/d5")
import groups
import numpy as np
for name in sys.argv[1:]:
    T = groups.build(name)
    N = len(T)
    arr = np.array(T, dtype=np.uint16)
    with open(f"/home/user/degree-diameter/research/squads/beyond13/r6/i16/out/tab_{name}.bin", "wb") as f:
        f.write(struct.pack("<i", N))
        f.write(arr.tobytes())
    print(name, N, "ok")
