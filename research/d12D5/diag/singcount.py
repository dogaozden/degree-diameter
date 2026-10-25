import pickle, itertools
from collections import Counter
D = pickle.load(open('complete.pkl', 'rb')); TRI, SOLS, PTS = D['TRI'], D['sols'], D['PTS']
def norm(v):
    v = tuple(x % 3 for x in v)
    for x in v:
        if x: return tuple((y * x) % 3 for y in v)
E = [tuple(int(r == i) for r in range(4)) for i in range(4)]
def line(u, v): return frozenset(norm(tuple(a * x + b * y for x, y in zip(u, v))) for a in range(3) for b in range(3) if (a, b) != (0, 0))
cnt = Counter()
for s in SOLS:
    legs = [[line(E[i], q) for q in TRI[i][s[i]]] for i in range(4)]
    inter = sum(1 for i, j in itertools.combinations(range(4), 2) for L in legs[i] for M in legs[j] if L & M)
    cnt[inter] += 1
print(sorted(cnt.items()))
