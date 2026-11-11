# random cubic bipartite girth>=6 base with h+h vertices: union of 3 random perfect matchings, no repeated edge, no 4-cycle
import random, sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/beyond13/r4/g02")
from mkbases import check, write
def gen(h, rng):
    for _ in range(200000):
        E = set(); ok = True
        for _k in range(3):
            p = list(range(h)); rng.shuffle(p)
            for a in range(h):
                e = (a, h + p[a])
                if e in E: ok = False; break
                E.add(e)
            if not ok: break
        if not ok: continue
        n = 2 * h
        Eu = sorted((a, b) for a, b in E)
        col = {i: (0 if i < h else 1) for i in range(n)}
        # cycle-free-of-4 check via girth
        bip, girth, _ = check(n, [tuple(sorted(e)) for e in Eu])
        if girth >= 6: return n, [tuple(sorted(e)) for e in Eu], col
    return None
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
r = gen(16, rng)
n, E, col = r
bip, girth, _ = check(n, E)
print("rnd32 girth", girth, "bip", bip, "edges", len(E))
write("/home/user/degree-diameter/research/squads/beyond13/r4/g02/rndg6_32.txt", n, E, col)
