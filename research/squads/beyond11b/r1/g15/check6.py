import random, sys
sys.argv = ['x', '2', '3', '1', '17']
from check import *
rng = random.Random(23); D = 5
def orbit(x): return [x, alpha(x), alpha(alpha(x))]
def neg(x): return ((((-x[0][0])%p, (-x[0][1])%p, (-x[0][2])%p, (-x[0][3])%p)), x[1])
def forced(rng):
    while True:
        x = els[rng.randrange(N)]
        orb = orbit(x); orb2 = [neg(y) for y in orb]
        ids = {idx[y] for y in orb + orb2}
        if len(ids) < 6 or idx[e] in ids: continue
        S = orb + orb2
        while len(S) < 9:
            o = orbit(els[rng.randrange(N)]); oi = {idx[z] for z in o}
            cur = {idx[z] for z in S}
            if len(oi) == 3 and not (oi & cur) and idx[e] not in oi: S += o
        return S
cen = lambda g: g[0] in [(1,0,0,1),(4,0,0,4)]
res = {'rand': [], 'forced': []}
for name, gen in (('rand', lambda: random_S(3, rng)), ('forced', lambda: forced(rng))):
    for t in range(40):
        S = gen(); dist = bfs(S)
        unc = [els[i] for i in range(N) if dist[0][i] < 0 or dist[0][i] > D]
        uncB = [els[i] for i in range(N) if dist[1][i] < 0 or dist[1][i] > D]
        res[name].append((len(unc), len(uncB), sum(1 for g in unc if cen(g)), sum(1 for g in uncB if cen(g))))
    arr = res[name]
    print(name, "mean uncovered A,B:", sum(a for a,_,_,_ in arr)/len(arr), sum(b for _,b,_,_ in arr)/len(arr),
          " frac trials with diam ok:", sum(1 for a,b,_,_ in arr if a==0 and b==0)/len(arr),
          " central uncovered A,B mean:", sum(c for _,_,c,_ in arr)/len(arr), sum(d for _,_,_,d in arr)/len(arr))
