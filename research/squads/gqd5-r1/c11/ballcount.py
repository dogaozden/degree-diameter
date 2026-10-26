import sys, os
os.environ["OMP_NUM_THREADS"] = "1"; os.environ["OPENBLAS_NUM_THREADS"] = "1"
sys.argv = ['x', '4', '2', '1', '7']
exec(open('hubsearch.py').read().split('Y = random_Y()')[0])
Y = random_Y()
A = B0.copy()
for h, g in Y:
    A[nv + h, nv + K + g] = 1; A[nv + K + g, nv + h] = 1
V = I[HUBS].copy()
for _ in range(5):
    V = np.minimum(V + V @ A, 1.0)
Bidx = np.arange(K)
within = V[:, nv + Bidx] > 0          # rows: hubs, cols: B-hubs
bh = within[:K]                       # B-hub rows
print('K =', K, 'B-hubs; max #B-hubs within distance 5 of a B-hub:', int(bh.sum(1).max()) - 1,
      'min:', int(bh.sum(1).min()) - 1)
ah = V[:K, nv + K + np.arange(K)] > 0
print('max #A-hubs within 5 of a B-hub:', int(ah.sum(1).max()))
