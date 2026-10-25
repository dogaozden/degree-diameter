import numpy as np, sys, json, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c3')
import gen
from gen import *
rng = np.random.default_rng(4)
samp = sample_K(rng, 6000)
from collections import Counter, defaultdict
byord = defaultdict(list)
for Xm, Ym, T in samp:
    o = mat_order(T)
    byord[o].append((Xm, Ym, T))
print('V4 action orders (sample of 6000):', sorted((k, len(v)) for k, v in byord.items() if k))
# rotation orders
for a in range(1, 12):
    R = rot_mat(a)
    assert np.all((R.T @ M @ R) % p == M)
    print('rot^%d order' % a, mat_order(R[np.ix_(range(6), range(6))] if False else R, cap=100))
pickle.dump({k: v[:6] for k, v in byord.items() if k}, open('/home/user/degree-diameter/research/squads/d14D7-r4/c3/k_samples.pkl', 'wb'))
