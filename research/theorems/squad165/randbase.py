"""Random connected 4-regular bipartite base multigraphs on k + k vertices (union of 4 random perfect matchings,
multi-edges allowed).  usage: python3 randbase.py k count seed outdir"""
import sys, random, os
k, cnt, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed); os.makedirs(out, exist_ok=True)
def connected(E):
    adj = {}
    for a, b in E:
        adj.setdefault(('a', a), set()).add(('b', b)); adj.setdefault(('b', b), set()).add(('a', a))
    st = [('a', 0)]; seen = {('a', 0)}
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == 2 * k
made = 0
while made < cnt:
    E = []
    for _ in range(4):
        p = list(range(k)); rng.shuffle(p); E += [(a, p[a]) for a in range(k)]
    if not connected(E): continue
    with open(f'{out}/r{k}_{seed}_{made:03d}.txt', 'w') as f:
        f.write(f'{k}\n' + ''.join(f'{a} {b}\n' for a, b in E))
    made += 1
