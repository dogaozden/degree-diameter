import random, time, sys
from collections import Counter
sys.argv = [sys.argv[0]]
import bicoset as bc
rng = random.Random(1)
VA = [9, 37, 55, 52]; VB = [49, 5, 17, 8]; x = (28, 2, 31, 51)
t0 = time.time()
A = [(1, t, 0, 1) for t in bc.span(VA)]
B = [(1, t, 0, 1) for t in bc.span(VB)]
xi = bc.minv(x)
def keyA(g): return min(bc.mmul(a, g) for a in A)
def keyB(g): return min(bc.mmul(b, g) for b in B)
def nbrs(node):
    side, g = node
    if side == 'A': return {('B', keyB(bc.mmul(bc.mmul(xi, a), g))) for a in A}
    return {('A', keyA(bc.mmul(bc.mmul(x, b), g))) for b in B}
from collections import deque
for s in [('A', keyA((1,0,0,1))), ('B', keyB((1,0,0,1)))]:
    dist = {s: 0}; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in nbrs(u):
            if w not in dist: dist[w] = dist[u] + 1; dq.append(w)
    print('source', s[0], 'distance histogram', sorted(Counter(dist.values()).items()))
print('time', round(time.time() - t0, 1), 's')
