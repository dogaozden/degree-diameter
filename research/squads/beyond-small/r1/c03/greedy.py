import numpy as np, sys
W=264; HALF=16896
balls = np.fromfile('ball3.bin', dtype=np.uint64).reshape(HALF, W)
# popcount table over bytes
def popcnt_rows(M):
    b = M.view(np.uint8)
    return np.unpackbits(b, axis=1).sum(axis=1)
unc = np.zeros(W, dtype=np.uint64)
# all A-vertices 0..16895 uncovered
full = np.zeros(HALF, dtype=np.uint8); full[:]=1
unc = np.packbits(full, bitorder='little').view(np.uint64).copy()
print('uncovered init', popcnt_rows(unc[None,:])[0])
chosen=[]
for step in range(40):
    gain = popcnt_rows(balls & unc[None,:])
    best = int(gain.argmax())
    chosen.append((best, int(gain[best])))
    unc = unc & ~balls[best]
    left = int(popcnt_rows(unc[None,:])[0])
    print(step+1, 'vertex', best+HALF, 'gain', int(gain[best]), 'uncovered left', left, flush=True)
    if left==0: break
