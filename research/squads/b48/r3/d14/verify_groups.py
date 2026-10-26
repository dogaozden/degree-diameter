import sys, glob, numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
for f in sorted(glob.glob("/home/user/degree-diameter/research/squads/b48/r3/d14/tabs/*.bin")):
    with open(f, "rb") as fh:
        N = int(np.fromfile(fh, dtype=np.int32, count=1)[0])
        T = np.fromfile(fh, dtype=np.uint16, count=N * N).reshape(N, N)
    groups.check(T)
    inv = sum(1 for g in range(1, N) if T[g, g] == 0)
    ab = bool((T == T.T).all())
    print(f.split("/")[-1], N, "involutions", inv, "abelian", ab, flush=True)
