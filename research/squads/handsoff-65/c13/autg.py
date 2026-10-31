# automorphisms of G (table g342.txt) that preserve S; prints those with fixed points (order 2 preferred)
import random, sys
tab = open('g342.txt').read().split()
m = int(tab[0]); T = [[int(tab[1 + i * m + j]) for j in range(m)] for i in range(m)]
S = {106, 241, 112, 304, 137, 24}
def closure(gens):
    seen = {0}; fr = [0]
    while fr:
        x = fr.pop()
        for g in gens:
            y = T[x][g]
            if y not in seen: seen.add(y); fr.append(y)
    return len(seen)
random.seed(1)
gens = None
for _ in range(10000):
    a, b = random.sample(range(1, m), 2)
    if closure([a, b]) == m: gens = [a, b]; break
print('generators', gens)
# BFS words: word[x] = (parent, gen index) on Cayley graph with right mult by gens
par = {0: None}; order = [0]
for x in order:
    for gi, g in enumerate(gens):
        y = T[x][g]
        if y not in par: par[y] = (x, gi); order.append(y)
def ordr(x):
    k = 1; y = x
    while y != 0: y = T[y][x]; k += 1
    return k
def try_img(h1, h2):
    img = {0: 0}; hg = [h1, h2]
    for y in order[1:]:
        p, gi = par[y]; img[y] = T[img[p]][hg[gi]]
    if len(set(img.values())) != m: return None
    # homomorphism check: img[x*g] = img[x]*img[g]
    for x in range(m):
        for gi, g in enumerate(gens):
            if img[T[x][g]] != T[img[x]][hg[gi]]: return None
    return img
found = []
for h1 in range(1, m):
    if ordr(h1) != ordr(gens[0]): continue
    for h2 in range(1, m):
        if ordr(h2) != ordr(gens[1]): continue
        img = try_img(h1, h2)
        if img is None: continue
        if {img[s] for s in S} == S:
            fix = sum(1 for x in range(m) if img[x] == x)
            found.append((h1, h2, fix))
print('automorphisms preserving S:', len(found))
for h1, h2, fix in found[:40]:
    print(h1, h2, 'fixed', fix)
