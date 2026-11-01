# Trade-off test: diameter <= D (exact, from BFS eccentricities of (e,A),(e,B)) for random alpha-invariant S (f=0)
# versus S that also contains an orbit of -s (forcing -I into S^-1 S). Same Delta.
import random, sys
from check import *
h = int(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]); seed = int(sys.argv[4]); D = 2*h+1
rng = random.Random(seed)
def diam_ok(S):
    dist = bfs(S)
    return all(d >= 0 and d <= D for d in dist[0]) and all(d >= 0 and d <= D for d in dist[1])
def orbit(x): return [x, alpha(x), alpha(alpha(x))]
def neg(x): return (((p-x[0][0])%p, (p-x[0][1])%p, (p-x[0][2])%p, (p-x[0][3])%p), x[1]) if False else ((( (-x[0][0])%p, (-x[0][1])%p, (-x[0][2])%p, (-x[0][3])%p)), x[1])
def forced_S(rng):
    while True:
        x = els[rng.randrange(N)]
        if x[0] in [(1,0,0,1)] and x[1]==0: continue
        orb = orbit(x); orb2 = [neg(y) for y in orb]
        ids = [idx[y] for y in orb + orb2]
        if len(set(ids)) < 6 or idx[e] in ids: continue
        S = orb + orb2
        # fill remaining with random orbits
        while len(S) < 3*m:
            y = els[rng.randrange(N)]
            o = orbit(y)
            if len({idx[z] for z in o}) == 3 and not ({idx[z] for z in o} & {idx[z] for z in S}) and idx[e] not in {idx[z] for z in o}:
                S += o
        return S
ok_rand = ok_forced = 0
for t in range(trials):
    Sr = random_S(m, rng); ok_rand += diam_ok(Sr)
    Sf = forced_S(rng); ok_forced += diam_ok(Sf)
print(f"h={h} D={D} Delta={3*m} trials={trials}: diam<=D random S {ok_rand}/{trials}; S with -s,s forced {ok_forced}/{trials}")
