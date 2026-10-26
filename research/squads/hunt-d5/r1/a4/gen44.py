import random, itertools
random.seed(4444)
perms = list(itertools.permutations(range(4)))
def connected(M):
    vis = {('a',0)}; st = [('a',0)]
    while st:
        s, x = st.pop()
        nb = [('b',j) for j in range(4) if M[x][j]] if s == 'a' else [('a',i) for i in range(4) if M[i][x]]
        for y in nb:
            if y not in vis: vis.add(y); st.append(y)
    return len(vis) == 8
seen = set(); out = []
for _ in range(20000):
    if len(out) >= 20: break
    ps = [random.choice(perms) for _ in range(5)]
    M = [[0]*4 for _ in range(4)]
    for p in ps:
        for i in range(4): M[i][p[i]] += 1
    if max(max(r) for r in M) > 2 or not connected(M): continue
    # cheap invariant: sorted multiset of row-sorted entries, to avoid near-duplicates
    key = (tuple(sorted(tuple(sorted(r)) for r in M)), tuple(sorted(tuple(sorted(c)) for c in zip(*M))))
    if key in seen: continue
    seen.add(key); out.append(M)
for k, M in enumerate(out):
    edges = [(i, 4+j) for i in range(4) for j in range(4) for _ in range(M[i][j])]
    with open(f"base44_{k:02d}.txt", "w") as f:
        f.write(f"8 {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
    print(k, M)
print(len(out), "bases")
