# iterated local search helper: perturb k random edge voltages of a volt file (format of w3s write_lift)
import random, sys
src, dst, k, seed, N = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
random.seed(seed)
L = open(src).read().split('\n')
hdr = L[0]
rows = [l.split() for l in L[1:] if l.strip()]
for _ in range(k):
    i = random.randrange(len(rows))
    rows[i][2] = str(random.randrange(N))
with open(dst, 'w') as f:
    f.write(hdr + '\n')
    for r in rows: f.write(' '.join(r) + '\n')
