import sys
from collections import Counter
t = open(sys.argv[1]).read().split(); n = int(t[0]); h = n // 2
E = [(int(t[1+2*i]), int(t[2+2*i])) for i in range((len(t)-1)//2)]
deg = Counter()
for u, v in E: deg[u] += 1; deg[v] += 1
print('n', n, 'edges', len(E), 'cubic', all(deg[x] == 3 for x in range(n)), 'bip', all((u < h) != (v < h) for u, v in E), 'simple', len(set(map(lambda e: tuple(sorted(e)), E))) == len(E))
