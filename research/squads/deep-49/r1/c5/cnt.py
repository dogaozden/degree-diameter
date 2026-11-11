# count, for each B vertex w, the X-edges between N(0) and N(w) (diagnostic for the matching condition)
import collections, sys
E = [tuple(map(int, l.split())) for l in open('/home/user/degree-diameter/research/squads/deep-49/seeds/valid4970.edges').read().split('\n')[1:] if l.strip()]
nbr = collections.defaultdict(list)
for u, v in E:
    nbr[u].append(v); nbr[v].append(u)
N0 = set(nbr[0])
hist = collections.Counter()
best = []
for w in range(2485, 4970):
    Nw = set(nbr[w])
    cross = sum(1 for q in Nw for p in nbr[q] if p in N0)  # edges between N(w) and N(0) (q in A, p in B)
    cross = sum(1 for q in Nw for p in nbr[q] if p in N0)
    hist[cross] += 1
print('B vertices w by number of X-edges between N(w) and N(0):', sorted(hist.items()))
print('dist-1 or dist-3 check: |B within 3 of 0| =', sum(1 for w in range(2485,4970) if any(p in set(nbr[w]) for p in N0) or w in N0))
