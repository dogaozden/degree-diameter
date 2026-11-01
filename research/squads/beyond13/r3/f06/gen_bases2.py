import random, itertools, math
out = "/home/user/degree-diameter/research/squads/beyond13/r3/f06/bases"
def write(name, b, edges):
    with open(f"{out}/{name}.txt", "w") as f:
        f.write(f"{b}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
def cost(h, nb):
    c = 0
    for i, j in itertools.combinations(range(h), 2):
        c += max(0, len(nb[i] & nb[j]) - 1)
    return c
def rand_girth6(h, d, seed, iters=200000):
    rnd = random.Random(seed)
    # start: circulant-free random d-regular via shifts, then switch moves
    nb = [set() for _ in range(h)]
    for k in range(d):
        perm = list(range(h)); rnd.shuffle(perm)
        for i in range(h): nb[i].add(perm[i])
    # ensure simple: rebuild by pairing if collision (retry until sets have size d)
    while any(len(s) != d for s in nb):
        nb = [set() for _ in range(h)]
        for k in range(d):
            perm = list(range(h)); rnd.shuffle(perm)
            for i in range(h): nb[i].add(perm[i])
    # B-degree also d automatically? sets from perms: each B vertex gets d edges only if no collisions; check
    cur = cost(h, nb)
    T = 1.0
    for it in range(iters):
        if cur == 0: break
        i1, i2 = rnd.sample(range(h), 2)
        # pick b1 in nb[i1]\nb[i2] and b2 in nb[i2]\nb[i1]: swap
        s1 = list(nb[i1] - nb[i2]); s2 = list(nb[i2] - nb[i1])
        if not s1 or not s2: continue
        b1 = rnd.choice(s1); b2 = rnd.choice(s2)
        # move: i1 gets b2 instead of b1, i2 gets b1 instead of b2 (keeps B-degrees)
        nb[i1].discard(b1); nb[i1].add(b2); nb[i2].discard(b2); nb[i2].add(b1)
        new = cost(h, nb)
        if new <= cur or rnd.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            nb[i1].discard(b2); nb[i1].add(b1); nb[i2].discard(b1); nb[i2].add(b2)
        T = max(0.05, T * 0.9995)
    if cur != 0: return None
    return [(i, h + j) for i in range(h) for j in sorted(nb[i])]
import sys
for h, s in [(21, 11), (24, 12), (27, 13)]:
    e = rand_girth6(h, 5, s, iters=20000)
    if e is None: print("fail", h); continue
    write(f"rg6_{2*h}_s{s}", 2 * h, e); print("ok", h)
