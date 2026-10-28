"""anneal_hub.py K NL NP STEPS SEED: choose K deleted matching edges; attach NL line-hubs to point-ends (split
evenly) and NP point-hubs to line-ends. Cost = pairs at distance > 5 (plus 1000 per degree violation).
Prints the best state as JSON-ish line."""
import sys, random, math, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c14')
from surg import match, bad, n0
K, NL, NP, STEPS, SEED = map(int, sys.argv[1:6])
random.seed(SEED)
def hubs_for(sel):
    # sel: list of match indices; point-ends and line-ends
    pe = [match[i][0] for i in sel]; le = [match[i][1] for i in sel]
    H = []
    # line-hubs: consecutive chunks of point-ends (size K//NL); point-hubs: chunks of line-ends
    cl = K // NL if NL else 0; cp = K // NP if NP else 0
    for j in range(NL): H.append(pe[j * cl:(j + 1) * cl])
    for j in range(NP): H.append(le[j * cp:(j + 1) * cp])
    return H
def cost(sel):
    H = hubs_for(sel)
    b, md, out = bad(set(sel), H, f'a{SEED}')
    return b + 1000 * max(0, md - 7), out
sel = random.sample(range(len(match)), K)
c, out = cost(sel)
best = (c, list(sel), out)
T0, T1 = 3.0, 0.2
for it in range(STEPS):
    T = T0 * (T1 / T0) ** (it / STEPS)
    new = list(sel)
    i = random.randrange(K)
    cand = random.randrange(len(match))
    if cand in new: continue
    new[i] = cand
    nc, nout = cost(new)
    if nc <= c or random.random() < math.exp(-(nc - c) / T):
        sel, c = new, nc
        if c < best[0]:
            best = (c, list(sel), nout)
            print('it', it, 'cost', c, flush=True)
            if c == 0: break
print('BEST', best[0], json.dumps(best[1]), flush=True)
print(best[2])
