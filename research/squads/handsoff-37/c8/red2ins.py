# Reduce conder168 by one vertex pair (remove adjacent a-b, reconnect the 4 outer neighbours in 2 ways -> n = 166),
# then insert two pairs greedily (insbest twice, exhaustive best 2-edge insertion each time) -> n = 170.
# Prints one line per option: option id, far at 170; keeps the best graphs in out/r2i_best*.edges
import subprocess, sys, os
src = '../shared/seeds/conder168.edges'
L = open(src).read().split(); n = int(L[0])
E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
A = set(range(84))  # conder168: A = 0..83
adj = {v: set() for v in range(n)}
for a, b in E: adj[a].add(b); adj[b].add(a)
def write(fn, nn, edges):
    with open(fn, 'w') as f:
        f.write(f"{nn}\n"); [f.write(f"{u} {v}\n") for u, v in edges]
best = (10**9, None)
opts = 0
for a, b in E:
    if a not in A: a, b = b, a
    a1, a2 = sorted(adj[a] - {b}); b1, b2 = sorted(adj[b] - {a})
    for (p, q), (r, s) in (((a1, b1), (a2, b2)), ((a1, b2), (a2, b1))):
        # relabel: remove a, b; keep others; new edges p-q, r-s (A-B pairs); need simple
        if q in adj[p] or s in adj[r]: continue
        # build 166-vertex graph with labels compacted
        keep = [v for v in range(n) if v not in (a, b)]
        idx = {v: i for i, v in enumerate(keep)}
        edges = [(idx[u], idx[v]) for u, v in E if a not in (u, v) and b not in (u, v)]
        edges += [(idx[p], idx[q]), (idx[r], idx[s])]
        fn1 = 'out/r2i_166.edges'; fn2 = 'out/r2i_168.edges'; fn3 = 'out/r2i_170.edges'
        write(fn1, n - 2, edges)
        o1 = subprocess.run(['./insbest', fn1, fn2], capture_output=True, text=True).stdout.strip()
        o2 = subprocess.run(['./insbest', fn2, fn3], capture_output=True, text=True).stdout.strip()
        opts += 1
        far170 = int(o2)
        print(f"opt {opts} remove({a},{b}) reconnect({p}-{q},{r}-{s}) far166_ins1={o1} far170={far170}", flush=True)
        if far170 < best[0]:
            best = (far170, fn3); os.system(f"cp {fn3} out/r2i_best.edges")
print("BEST", best[0], "options", opts, flush=True)
