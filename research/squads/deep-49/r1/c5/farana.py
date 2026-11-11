# Far-pair anatomy of a surgered graph: BFS from a few sources only (a*, b*, endpoints of the deleted edges).
import sys, collections
fn = sys.argv[1]
L = open(fn).read().split('\n')
n = int(L[0]); adj = collections.defaultdict(list)
for l in L[1:]:
    if l.strip():
        u, v = map(int, l.split()); adj[u].append(v); adj[v].append(u)
def bfs(s):
    d = {s: 0}; q = collections.deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in d: d[y] = d[x] + 1; q.append(y)
    return d
AS, BS = 4970, 4971
X = {}
base = {}
for l in open('/home/user/degree-diameter/research/squads/deep-49/seeds/valid4970.edges').read().split('\n')[1:]:
    if l.strip():
        u, v = map(int, l.split()); base.setdefault(u, set()).add(v); base.setdefault(v, set()).add(u)
# deleted edges = base edges no longer present
new = set()
for x in range(n):
    for y in adj[x]:
        new.add((min(x, y), max(x, y)))
old = set((min(x, y), max(x, y)) for x in base for y in base[x])
dele = sorted(old - new)
ends = sorted(set(v for e in dele for v in e))
print('deleted edges', dele)
for s in [AS, BS] + ends:
    d = bfs(s)
    far = [t for t in range(n) if d.get(t, 99) > 9]
    print('source', s, 'far targets', len(far), 'max dist', max(d.values()))
