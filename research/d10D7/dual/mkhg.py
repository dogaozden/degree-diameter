"""Random bipartite hub graph: union of d perfect matchings on H + H hubs, repaired so no edge repeats.
   python3 mkhg.py H d seed out"""
import random, sys
H, d, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed); adj = [set() for _ in range(H)]; edges = []
for m in range(d):
    perm = list(range(H)); rng.shuffle(perm)
    for _ in range(1000):
        bad = 0
        for j in range(H):
            if perm[j] in adj[j]:
                bad += 1
                for _ in range(100):
                    r = rng.randrange(H)
                    if perm[r] not in adj[j] and perm[j] not in adj[r]:
                        perm[j], perm[r] = perm[r], perm[j]; break
        if not bad: break
    for j in range(H):
        if perm[j] not in adj[j]: adj[j].add(perm[j]); edges.append((j, perm[j]))
with open(out, 'w') as f:
    f.write(f"{H} {len(edges)}\n"); f.writelines(f"{a} {b}\n" for a, b in edges)
