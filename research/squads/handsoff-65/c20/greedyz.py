# greedy choice of the dropped edge (w, z) for each covering vertex w, by exact far-pair count (python BFS)
import sys, random
from collections import deque
random.seed(int(sys.argv[1])); out = sys.argv[2]
t = open('../c7/h684.edges').read().split(); n = int(t[0]); E0 = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
S = [int(x) for x in open('cover_S.txt').read().split()]
base = set(tuple(sorted(e)) for e in E0)
A_nb = {}
adj0 = {v: set() for v in range(n)}
for a, b in base: adj0[a].add(b); adj0[b].add(a)
col = {0: 0}; q = [0]
for x in q:
    for y in adj0[x]:
        if y not in col: col[y] = 1 - col[x]; q.append(y)
u = n; N = n + 1
def bad(edges):
    adj = [[] for _ in range(N)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    tot = 0
    for s in range(N):
        d = [-1]*N; d[s] = 0; dq = [s]
        for x in dq:
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
        for tt in range(s+1, N):
            if d[tt] < 0 or d[tt] > 5: tot += 1
    return tot
edges = set(base)
zchoice = {}
for w in S:
    zs = [z for z in adj0[w] if col[z] == 0]
    zchoice[w] = zs
# start from random choice, then coordinate descent over the 6 choices
cur = {w: random.choice(zchoice[w]) for w in S}
def build(ch):
    E = set(base)
    for w in S:
        E.discard(tuple(sorted((w, ch[w])))); E.add(tuple(sorted((w, u))))
    return E
best = bad(build(cur)); print("init", best, flush=True)
for rnd_ in range(2):
    for w in S:
        for z in zchoice[w]:
            trial = dict(cur); trial[w] = z
            c = bad(build(trial))
            if c < best: best = c; cur = trial; print("improve", w, z, best, flush=True)
E = build(cur)
with open(out, 'w') as f:
    f.write("%d\n" % N)
    for a, b in sorted(E): f.write("%d %d\n" % (a, b))
print("final", best)
