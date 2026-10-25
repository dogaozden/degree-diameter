"""Random connected 4-regular bipartite multigraph bases on k+k vertices: union of 4 random permutations.
usage: python3 gen_bases.py K COUNT OUTDIR SEED"""
import random, sys, os
k, cnt, outdir, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
os.makedirs(outdir, exist_ok=True)
rng = random.Random(seed)
def connected(edges):
    adjA = {i: [] for i in range(k)}; adjB = {j: [] for j in range(k)}
    for a, b in edges: adjA[a].append(b); adjB[b].append(a)
    seen = {('a', 0)}; st = [('a', 0)]
    while st:
        s, x = st.pop()
        nb = adjA[x] if s == 'a' else adjB[x]
        for y in nb:
            t = ('b', y) if s == 'a' else ('a', y)
            if t not in seen: seen.add(t); st.append(t)
    return len(seen) == 2 * k
made = 0
while made < cnt:
    perms = [rng.sample(range(k), k) for _ in range(4)]
    edges = [(i, perms[t][i]) for t in range(4) for i in range(k)]
    rng.shuffle(edges)
    if not connected(edges): continue
    with open(f'{outdir}/k{k}_s{seed}_{made}.txt', 'w') as f:
        f.write(f'{k}\n')
        for a, b in edges: f.write(f'{a} {b}\n')
    par = len(edges) - len(set(edges))
    print(f'k{k}_s{seed}_{made}', 'parallel_edges', par)
    made += 1
