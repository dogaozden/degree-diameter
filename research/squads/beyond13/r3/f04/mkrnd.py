import random, sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/beyond13/r3/f04")
from mkbases import write
def bad(nb, h):
    # number of pairs of A vertices sharing >1 neighbour (excess counted)
    c = 0
    for a1 in range(h):
        for a2 in range(a1+1, h):
            k = len(nb[a1] & nb[a2])
            if k > 1: c += k*(k-1)//2
    return c
def make(h, seed, name):
    rng = random.Random(seed)
    # random start: each B vertex gets 4 A-neighbours via 4 random matchings (multi-edges avoided by retry)
    while True:
        nb = {a: set() for a in range(h)}
        okk = True
        for k in range(4):
            perm = list(range(h)); rng.shuffle(perm)
            for a in range(h):
                if perm[a] in nb[a]: okk = False; break
                nb[a].add(perm[a])
            if not okk: break
        if okk: break
    cur = bad(nb, h)
    T = 1.0
    for it in range(400000):
        if cur == 0: break
        a1, a2 = rng.sample(range(h), 2)
        x = rng.choice(list(nb[a1])); y = rng.choice(list(nb[a2]))
        if y in nb[a1] or x in nb[a2]: continue
        nb[a1].remove(x); nb[a2].remove(y); nb[a1].add(y); nb[a2].add(x)
        c = bad(nb, h)
        if c <= cur or rng.random() < 2.718 ** (-(c-cur)/T):
            cur = c
        else:
            nb[a1].remove(y); nb[a2].remove(x); nb[a1].add(x); nb[a2].add(y)
        T = max(0.05, T*0.99997)
    print(name, "bad", cur, it)
    assert cur == 0
    E = sorted((a, h + bb) for a in range(h) for bb in nb[a])
    write(name, 2*h, E)
make(14, 1, "g6r4_28.txt")
make(15, 2, "g6r4_30.txt")
make(20, 3, "g6r4_40.txt")
make(30, 4, "g6r4_60.txt")
