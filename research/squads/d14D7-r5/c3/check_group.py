import sys, random, numpy as np
exec(open('frames2.py').read().split("t0=time.time()")[0])
fr=frames_exact(U_imag)
def tomod(Fc): return np.array([[(Fc[c][r+1]*6)%11 for c in range(7)] for r in range(7)],dtype=np.int64)
allm=[tomod(F) for F in fr]
rng=random.Random(5)
for trial in range(3):
    gens=[rng.choice(allm) for _ in range(2)]
    H=closure(gens, cap=200000)
    print('closure of 2 random frames (cap 200000):', None if H is None else len(H), flush=True)
# is the frame set closed under multiplication?
keys=set(m.tobytes() for m in allm)
ok=0
for _ in range(300):
    a=rng.choice(allm); b=rng.choice(allm)
    ok += ((a@b)%11).tobytes() in keys
print('random products that are frames:', ok, '/300')
