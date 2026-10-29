"""q=5: exact max clique through vertex 0 for every projective direction u with Qp(u) non-square (u normalized
so its first nonzero coordinate is 1). Uses clq exact on the compatibility graph of each direction."""
import itertools, subprocess, os, numpy as np
from graph import build
from hexaffine import qp, is_square
p = 5
res = {}
dirs = []
for u in itertools.product(range(p), repeat=5):
    nz = [t for t in u if t]
    if not nz or nz[0] != 1:
        continue
    n = qp(u, p)
    if n == 0 or is_square(n, p):
        continue
    dirs.append(u)
print('nonsquare directions', len(dirs), flush=True)
os.makedirs('sweep_tmp', exist_ok=True)
hist = {}
for u in dirs:
    _, R, adj = build(p, u)
    fn = 'sweep_tmp/adj.bin'
    with open(fn, 'wb') as f:
        f.write(np.int32(len(R)).tobytes()); f.write(adj.astype(np.uint8).tobytes())
    out = subprocess.run(['./clq', 'exact', fn, '60'], capture_output=True, text=True).stdout
    k = int(out.split('=')[1].split('(')[0])
    hist[k] = hist.get(k, 0) + 1
print('histogram of max clique through 0 (k: number of directions):', hist, flush=True)
import shutil; shutil.rmtree('sweep_tmp')
