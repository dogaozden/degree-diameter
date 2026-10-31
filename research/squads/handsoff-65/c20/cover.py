# covering start for a new A-vertex u in the 684 Haar graph: choose 6 B-vertices whose 3-balls cover all A-vertices
import sys, random
from collections import deque
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
t = open('../c7/h684.edges').read().split(); n = int(t[0]); E = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
col = [-1]*n; col[0] = 0; q = deque([0])
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1-col[x]; q.append(y)
A = [v for v in range(n) if col[v] == 0]; B = [v for v in range(n) if col[v] == 1]
def ball3(w):
    d = {w: 0}; fr = [w]
    for depth in range(1, 4):
        nf = []
        for x in fr:
            for y in adj[x]:
                if y not in d: d[y] = depth; nf.append(y)
        fr = nf
    return set(v for v in d if col[v] == 0)
C = {w: ball3(w) for w in B}
print("ball3 sizes: min", min(len(c) for c in C.values()), "max", max(len(c) for c in C.values()), "of", len(A))
best = None
for trial in range(4000):
    S = []; cov = set()
    # randomized greedy: pick the B-vertex covering most uncovered A-vertices among a random sample
    for k in range(6):
        cand = random.sample(B, 60)
        w = max(cand, key=lambda w: (len(C[w] - cov), random.random()))
        S.append(w); cov |= C[w]
    if best is None or len(cov) > best[0]:
        best = (len(cov), S)
        print("trial", trial, "covered", len(cov), "of", len(A), flush=True)
    if len(cov) == len(A): break
print("BEST", best[0], best[1])
open('cover_S.txt', 'w').write(" ".join(map(str, best[1])))
