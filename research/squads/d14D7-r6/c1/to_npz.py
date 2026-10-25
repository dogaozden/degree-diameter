# convert a cann best-state text file (lines: "F .. k ..", "X ids", "L ids") to the .npz state format of mirror_build.py
import numpy as np, sys
txt, out = sys.argv[1], sys.argv[2]
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
lines = open(txt).read().split('\n')
X = np.array([int(v) for v in lines[1].split()[1:]], dtype=np.int64)
L = np.array([int(v) for v in lines[2].split()[1:]], dtype=np.int64)
R = np.load(SP + 'R756idx.npy').astype(np.int64)
assert len(X) == len(L)
np.savez(out, X=X, L=L, R=R)
print('wrote', out, 'k =', len(X))
