# Pappus graph (LCF [5,7,-7,7,-7,-5]^3 on Z18), relabelled so that side A = 0..8, side B = 9..17; writes lift base format
import sys, collections
lcf = [5,7,-7,7,-7,-5]*3
n = 18
E = set()
for i in range(n):
    E.add(tuple(sorted((i, (i+1) % n))))
    E.add(tuple(sorted((i, (i+lcf[i]) % n))))
adj = collections.defaultdict(list)
for a,b in E: adj[a].append(b); adj[b].append(a)
assert all(len(adj[v]) == 3 for v in range(n)), "not cubic"
col = {0: 0}; q = [0]
for v in q:
    for w in adj[v]:
        if w not in col: col[w] = 1 - col[v]; q.append(w)
assert all(col[a] != col[b] for a,b in E), "not bipartite"
A = [v for v in range(n) if col[v] == 0]; B = [v for v in range(n) if col[v] == 1]
lab = {v: i for i, v in enumerate(A + B)}
# diameter of base
def bfs(s):
    d = {s: 0}; q = [s]
    for v in q:
        for w in adj[v]:
            if w not in d: d[w] = d[v] + 1; q.append(w)
    return max(d.values())
print("base diameter", max(bfs(s) for s in range(n)), "sides", len(A), len(B), file=sys.stderr)
with open(sys.argv[1], "w") as f:
    f.write(f"{n}\n")
    for a,b in sorted(E):
        x, y = lab[a], lab[b]
        if x > y: x, y = y, x
        f.write(f"{x} {y}\n")
