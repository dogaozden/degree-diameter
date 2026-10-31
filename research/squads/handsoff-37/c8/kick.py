# usage: kick.py IN OUT K SEED : apply K random valid 2-switches (bipartite, simple kept) to a cubic bipartite edge list
import sys, random
src, dst, K, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
L = open(src).read().split(); n = int(L[0])
E = set()
for i in range(1, len(L), 2):
    a, b = int(L[i]), int(L[i+1]); E.add((min(a, b), max(a, b)))
# A side = colour 0 by BFS
adj = {v: set() for v in range(n)}
for a, b in E: adj[a].add(b); adj[b].add(a)
col = {0: 0}; q = [0]
for x in q:
    for y in adj[x]:
        if y not in col: col[y] = 1 - col[x]; q.append(y)
def AB(a, b): return (a, b) if col[a] == 0 else (b, a)
Es = [AB(a, b) for a, b in E]
E = set(Es)
done = 0
while done < K:
    i, j = random.sample(range(len(Es)), 2)
    (a, b), (a2, b2) = Es[i], Es[j]
    if a == a2 or b == b2: continue
    if (a, b2) in E or (a2, b) in E: continue
    Es[i] = (a, b2); Es[j] = (a2, b)
    E.discard((a, b)); E.discard((a2, b2)); E.add((a, b2)); E.add((a2, b))
    done += 1
with open(dst, 'w') as f:
    f.write(f"{n}\n")
    for a, b in Es: f.write(f"{a} {b}\n")
