import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path
fn = sys.argv[1]; N = int(sys.argv[2]); D = int(sys.argv[3])
with open(fn) as f:
    n = int(f.readline()); E = np.loadtxt(f, dtype=np.int64).reshape(-1, 2)
rows = np.concatenate([E[:, 0], E[:, 1]]); cols = np.concatenate([E[:, 1], E[:, 0]])
G = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(n, n))
srcs = [int(x) for x in sys.argv[4].split(',')]
dist = shortest_path(G, unweighted=True, directed=False, indices=srcs)
for s, row in zip(srcs, dist):
    far = np.where(row > D)[0]
    print("source", s, "ecc", int(row.max()), "num >D:", len(far), "examples:", far[:10].tolist(), "dists:", row[far[:10]].tolist() if len(far) else [])
