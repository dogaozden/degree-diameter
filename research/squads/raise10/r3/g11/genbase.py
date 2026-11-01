# random simple cubic bipartite base on h+h vertices (sides A=[0,h), B=[h,2h)); edges "a b" with b in [h,2h)
import random, sys
h = int(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]
random.seed(seed)
def conn(edges, nv):
    adj = [[] for _ in range(nv)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == nv
while True:
    es = set(); ok = True
    for _ in range(3):
        p = list(range(h)); random.shuffle(p)
        for a in range(h):
            e = (a, h + p[a])
            if e in es: ok = False
            es.add(e)
        if not ok: break
    if ok and conn(list(es), 2 * h): break
with open(out, 'w') as f:
    f.write(f"{2*h}\n")
    for a, b in sorted(es): f.write(f"{a} {b}\n")
print("wrote", out, len(es), "edges")
