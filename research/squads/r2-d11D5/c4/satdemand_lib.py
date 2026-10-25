from collections import Counter
from fail import load
def build_demands(path):
    n, dg, ln, sig = load(path)
    pt = [[] for _ in range(n)]
    for l in range(n):
        for p in ln[l]: pt[p].append(l)
    Coll = [set() for _ in range(n)]
    for l in range(n):
        for p in ln[l]: Coll[p].update(ln[l])
    for p in range(n): Coll[p].discard(p)
    Conc = [set() for _ in range(n)]
    for p in range(n):
        for l in pt[p]: Conc[l].update(pt[p])
    for l in range(n): Conc[l].discard(l)
    def demands(adj1, adj2):
        res = []
        for x in range(n):
            c2 = set()
            for a in adj1[x]:
                for y in adj2[a]:
                    if y != x: c2.add(y)
            c4 = Counter()
            for a in adj1[x]:
                for y in adj2[a]:
                    if y == x: continue
                    for b in adj1[y]:
                        if b == a: continue
                        for z in adj2[b]:
                            if z != y: c4[z] += 1
            for z in range(x + 1, n):
                if z in c2: continue
                if c4[z] <= 1: res.append((x, z))
        return res
    return n, dg, ln, sig, pt, Coll, Conc, demands(pt, ln), demands(ln, pt)
