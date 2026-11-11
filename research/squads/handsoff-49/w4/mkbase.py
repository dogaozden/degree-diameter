# mkbase.py: small 4-regular bipartite simple bases: K44 (b=8), K55-matching (b=10), random 4-regular bipartite
import random, sys
def write(name, b, edges):
    with open(name, 'w') as f:
        f.write(f"{b} {len(edges)}\n" + "".join(f"{u} {v}\n" for u, v in edges))
write('k44.txt', 8, [(i, 4+j) for i in range(4) for j in range(4)])
write('k55m.txt', 10, [(i, 5+j) for i in range(5) for j in range(5) if i != j])
def rand_bip(h, seed):
    # h + h vertices, 4-regular, simple: union of 4 random perfect matchings avoiding repeats
    rnd = random.Random(seed)
    while True:
        E = set(); ok = True
        for _ in range(4):
            for attempt in range(200):
                p = list(range(h)); rnd.shuffle(p)
                new = [(i, h+p[i]) for i in range(h)]
                if all(e not in E for e in new):
                    E.update(new); break
            else:
                ok = False; break
        if ok: return sorted(E)
for h in (6, 7):
    write(f'rb{2*h}.txt', 2*h, rand_bip(h, 11))
print("ok")
