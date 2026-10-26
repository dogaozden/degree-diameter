import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c14')
from surg import base, n0
from collections import defaultdict
adj = defaultdict(set)
for a, b in base: adj[a].add(b); adj[b].add(a)
def ball(s, r):
    d = {s: 0}; fr = [s]
    for k in range(r):
        nf = []
        for x in fr:
            for y in adj[x]:
                if y not in d: d[y] = k + 1; nf.append(y)
        fr = nf
    return d
# line-hub: candidate neighbours = point copies x<510; need lines (>=510) within 3 of some neighbour
C = {x: {y for y in ball(x, 3) if y >= 510} for x in range(510)}
P = {x: {y for y in ball(x, 4) if y < 510} for x in range(510, 1020)}  # for point-hubs: line neighbours cover points within 3 (dist from H = 1+3=4)
print('avg line-coverage per point copy', sum(len(v) for v in C.values()) / 510, 'max', max(len(v) for v in C.values()))
# point-hub: neighbours are line copies y>=510; need points within distance 3 of y (so within 4 of H)
Q = {y: {x for x in ball(y, 3) if x < 510} for y in range(510, 1020)}
print('avg point-coverage per line copy (dist<=3)', sum(len(v) for v in Q.values()) / 510, 'max', max(len(v) for v in Q.values()))
def greedy(cov, universe, k, trials=50):
    best = None
    for t in range(trials):
        rem = set(universe); chosen = []
        keys = list(cov)
        while rem and len(chosen) < k:
            random.shuffle(keys)
            x = max(keys, key=lambda z: len(cov[z] & rem) + random.random() * 0.5)
            chosen.append(x); rem -= cov[x]
        if best is None or len(rem) < best[0]: best = (len(rem), chosen)
    return best
print('line-hub 7-cover of 510 lines (uncovered count, set):', greedy(C, range(510, 1020), 7))
print('point-hub 7-cover of 510 points (uncovered, set):', greedy(Q, range(510), 7))
