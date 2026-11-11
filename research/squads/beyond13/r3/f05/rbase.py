# random simple 4-regular bipartite base, girth >= 6, via double-edge swaps minimising 4-cycles
import random, sys
def make(h, seed, steps=200000):
    rnd = random.Random(seed)
    # start: 4 cyclic shifts (simple since h >= 4)
    E = set()
    shifts = rnd.sample(range(h), 4)
    for s in shifts:
        for a in range(h): E.add((a, (a + s) % h))
    E = list(E)
    def bad(E):
        cnt = [[0]*h for _ in range(h)]
        nb = [[] for _ in range(h)]
        for a, b in E: nb[a].append(b)
        tot = 0
        for a in range(h):
            for c in range(a+1, h):
                k = len(set(nb[a]) & set(nb[c]))
                tot += k*(k-1)//2
        return tot
    cur = bad(E); Eset = set(E)
    T = 0.5
    for it in range(steps):
        if cur == 0: break
        i, j = rnd.randrange(len(E)), rnd.randrange(len(E))
        (a, b), (c, d) = E[i], E[j]
        if a == c or b == d: continue
        if (a, d) in Eset or (c, b) in Eset: continue
        E2 = E[:]; E2[i] = (a, d); E2[j] = (c, b)
        nv = bad(E2)
        if nv <= cur or rnd.random() < pow(2.718, -(nv-cur)/T):
            Eset.discard((a, b)); Eset.discard((c, d)); Eset.add((a, d)); Eset.add((c, b))
            E = E2; cur = nv
        T = max(0.05, T*0.9999)
    return E, cur
if __name__ == "__main__":
    h = int(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]
    E, cur = make(h, seed)
    print("h", h, "bad", cur)
    if cur == 0:
        with open(out, "w") as f:
            f.write(f"{2*h}\n")
            for a, b in E: f.write(f"{a} {h+b}\n")
