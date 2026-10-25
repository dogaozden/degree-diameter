"""Hub layout for x5gen2 / xgen (up to J hubs per side per freed point; J = 2 for 5 levels, 3 for 7): H line-side and H point-side hubs,
hub graph = union of DEG random perfect matchings without repeated edges (a matching that would repeat an edge is
redrawn). Owners: freed point j % K. Check the hub graph alone with apsp (diameter <= 7 suffices).
usage: python3 mkhubs_rand.py H K DEG seed out_hubs out_hubgraph_edges [J=2]"""
import sys, random
H, K, DEG, seed, out_hubs, out_edges = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
J = int(sys.argv[7]) if len(sys.argv) > 7 else 2
assert H <= J * K
rng = random.Random(seed); E = set()
for d in range(DEG):
    for tries in range(10000):
        perm = list(range(H)); rng.shuffle(perm)
        bad = [j for j in range(H) if (j, perm[j]) in E]
        for j in bad:                      # repair by swapping with random partners
            for _ in range(1000):
                t = rng.randrange(H)
                if (j, perm[t]) not in E and (t, perm[j]) not in E: perm[j], perm[t] = perm[t], perm[j]; break
        if all((j, perm[j]) not in E for j in range(H)): break
    E.update((j, perm[j]) for j in range(H))
edges = sorted(E); assert len(edges) == H * DEG
own = [j % K for j in range(H)]
with open(out_hubs, 'w') as o:
    o.write('%d %d %d\n' % (H, H, len(edges))); o.write(' '.join(map(str, own)) + '\n'); o.write(' '.join(map(str, own)) + '\n')
    o.writelines('%d %d\n' % e for e in edges)
with open(out_edges, 'w') as o:
    o.write('%d\n' % (2 * H)); o.writelines('%d %d\n' % (j, H + k) for j, k in edges)
print('H', H, 'edges', len(edges))
