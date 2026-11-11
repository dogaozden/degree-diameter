# random simple cubic bipartite bases, girth >= 6 (no 4-cycles), connected. Format: "2h" then 3h lines "a (h+b)".
import random, sys, os
out = '/home/user/degree-diameter/research/squads/beyond13/r3/f01/bases'
os.makedirs(out, exist_ok=True)
def gen(h, rng):
    while True:
        # configuration model with retries for simple + no C4
        for _ in range(2000):
            sb = [j for j in range(h) for _ in range(3)]
            rng.shuffle(sb)
            sa = [i for i in range(h) for _ in range(3)]
            E = list(zip(sa, sb))
            if len(set(E)) < len(E): continue
            adjA = [set() for _ in range(h)]
            for a, b in E: adjA[a].add(b)
            ok = True
            for a in range(h):
                for c in range(a + 1, h):
                    if len(adjA[a] & adjA[c]) >= 2: ok = False; break
                if not ok: break
            if not ok: continue
            par = list(range(2 * h))
            def f(x):
                while par[x] != x: par[x] = par[par[x]]; x = par[x]
                return x
            for a, b in E: par[f(a)] = f(h + b)
            if len({f(x) for x in range(2 * h)}) == 1: return E
if __name__ == '__main__':
    for h in [20, 24, 25, 27, 30]:
        for s in range(2):
            rng = random.Random(1000 * h + s)
            E = gen(h, rng)
            name = f'g6h{h}_{s}'
            with open(f'{out}/{name}.txt', 'w') as fh:
                fh.write(f'{2*h}\n')
                for a, b in E: fh.write(f'{a} {h+b}\n')
            print(name, 2 * h)
