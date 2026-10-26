import sys, numpy as np
with open(sys.argv[1],'rb') as f:
    N = int(np.frombuffer(f.read(4), dtype=np.int32)[0])
    T = np.frombuffer(f.read(), dtype=np.uint16).reshape(N, N).astype(np.int64)
gens = [int(x) for x in sys.argv[2:6]]
ball = {0}; front = {0}; sizes=[1]
for lev in range(9):
    nf = set()
    for x in front:
        for s in gens:
            y = int(T[x, s])
            if y not in ball: nf.add(y)
    ball |= nf; front = nf; sizes.append(len(ball))
print(sizes)
# also check inverse-closure and order of s
inv = {s: int(np.where(T[s]==0)[0][0]) for s in gens}
print('inv', inv)
