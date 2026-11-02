"""Which conjugacy classes of SL(2,5) x F21 are invariant under the Aut generators used by hx (r1 .aut file)?"""
import numpy as np
AUT = '/home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3.aut'
f = open(AUT); m = int(f.readline()); perms = [np.array(list(map(int, f.readline().split()))) for _ in range(m)]
cls = np.load('/home/user/degree-diameter/research/squads/deep-49/r2/a/cls.npy')
ncls = cls.max() + 1
for c in range(ncls):
    R = np.where(cls == c)[0]
    inv = all(set(P[R].tolist()) == set(R.tolist()) for P in perms)
    if inv or c in (16, 18, 26, 28, 36, 38, 31, 33):
        print('class', c, 'size', len(R), 'Aut-invariant' if inv else 'NOT Aut-invariant',
              'images under gens:', [sorted(set(cls[P[R]].tolist())) for P in perms])
print('aut gens', m)
