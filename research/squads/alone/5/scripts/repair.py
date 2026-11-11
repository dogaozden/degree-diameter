# twin graph tw_<seed>.e: find deficient vertices (deg 15), add a random perfect matching between deficient A and B
# (skipping existing edges) and write the result; prints the degree summary.
import sys, random
from graph import load
path, out, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
rnd = random.Random(seed)
n, adj, E = load(path)
defA = [v for v in range(n) if len(adj[v]) < 16 and v < n // 2 + 1 and v <= 15730]
defB = [v for v in range(n) if len(adj[v]) < 16 and v > 15730]
print('deficient A', len(defA), 'deficient B', len(defB), flush=True)
rnd.shuffle(defB)
for attempt in range(1000):
    rnd.shuffle(defB)
    pairs = list(zip(defA, defB))
    if all(b not in adj[a] for a, b in pairs):
        break
newE = E + pairs
with open(out, 'w') as f:
    f.write(f'{n}\n'); f.writelines(f'{u} {v}\n' for u, v in newE)
print('wrote', out, 'edges', len(newE), 'added', len(pairs))
