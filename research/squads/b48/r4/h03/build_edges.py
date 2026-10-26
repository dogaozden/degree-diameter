# h03: lift edge list from one flift eval line "0 a 0 0 b c" over base b22_cubic (left multiplication, (u,x)~(v,g x))
import sys, numpy as np
grp, line, out = sys.argv[1], sys.argv[2], sys.argv[3]
N = int(np.fromfile(grp, dtype=np.int32, count=1)[0])
T = np.fromfile(grp, dtype=np.uint16, offset=4).reshape(N, N).astype(np.int64)
volt = [int(v) for v in line.split()]
base = [(0,2),(0,2),(0,3),(1,2),(1,3),(1,3)]
edges = []
for (u,v),g in zip(base, volt):
    for x in range(N):
        edges.append((u*N+x, v*N+T[g,x]))
with open(out,'w') as f:
    f.write(f"{4*N}\n"); f.writelines(f"{a} {b}\n" for a,b in edges)
