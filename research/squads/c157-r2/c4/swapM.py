# swapM.py SRC DST SEED NSWAP: copy a d7hex solution file, exchanging NSWAP random pairs of entries of M (M stays a bijection)
import sys, random
src, dst, seed, nswap = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
lines = open(src).read().split('\n')
hi = next(i for i, l in enumerate(lines) if l.startswith('hubedges'))
head = lines[:hi + 1]
M = [int(x) for x in ' '.join(lines[hi + 1:]).split()]
N = len(M)
for _ in range(nswap):
    a, b = random.sample(range(N), 2)
    M[a], M[b] = M[b], M[a]
out = head + [' '.join(map(str, M[i:i + 20])) for i in range(0, N, 20)]
open(dst, 'w').write('\n'.join(out) + '\n')
print('swapped', nswap, 'pairs of M entries (seed', seed, ') ->', dst)
