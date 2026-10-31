import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from g2grp import *
import random, time
from collections import Counter, deque
random.seed(2)
E = pickle.load(open('/home/user/degree-diameter/research/squads/handsoff-65/c8/rootel.pkl', 'rb'))
print("elements", len(E))
adj = [[] for _ in range(P+L)]
for k, l in enumerate(lines):
    for z in l:
        adj[z].append(P+k); adj[P+k].append(z)
def bfs(s):
    d = [-1]*(P+L); d[s] = 0; q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if d[w] < 0: d[w] = d[u]+1; q.append(w)
    return sorted(Counter(d).items())
print("BFS from point 0:", bfs(0))
print("BFS from line P:", bfs(P))
t0 = time.time()
gens = []
for e in E[:30]:
    c = random.randrange(1, p)
    gens.append(unip([[ (c*x) % p for x in r] for r in e]))
g = [[int(i == j) for j in range(N)] for i in range(N)]
for _ in range(30):
    g = mat_mul(g, random.choice(gens))
perm = perm_of(g)
print("aut ok", is_aut(perm), "time", round(time.time()-t0, 2))
