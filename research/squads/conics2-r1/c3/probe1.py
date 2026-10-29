import time, numpy as np, random
from common import *
sig, R = load_rec()
print('base', score(sig, R))
# lines through R-collinear? just sample candidates
rng = random.Random(1)
cands = [x for x in range(N) if x not in R]
rng.shuffle(cands)
t=time.time()
res = []
for x in cands[:12]:
    res.append((score(sig, R+[x]), x))
print(time.time()-t)
print(sorted(res)[:12])
print(sorted(res)[-3:])
