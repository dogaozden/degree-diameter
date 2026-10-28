"""Line-group hubs: R = disjoint union of GQ lines S (a partial spread).  For each s in S:
B-hub hB_s joined to (y,1) for all y in s; A-hub hA_s joined to (y,2) for all y in s; edge hB_s - hA_s.
Degree of hub = (q+1) + 1 = q+2.  Each freed point is on exactly one group line."""
import sys, subprocess, random; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from base import *
APSP='/home/user/degree-diameter/research/theorems/d5gq/apsp'

def partial_spread(G, seed, tries=2000):
    rng = random.Random(seed)
    best = []
    for _ in range(tries):
        order = list(range(G.nl)); rng.shuffle(order)
        used = set(); S = []
        for s in order:
            if not (used & set(G.lines[s])):
                S.append(s); used |= set(G.lines[s])
        if len(S) > len(best): best = S
    return best

def line_hub_edges(G, S, M01):
    R = sorted(set(p for s in S for p in G.lines[s]))
    n0, E, per = base_edges(G, M01, R)
    nS = len(S)
    for i, s in enumerate(S):
        hb = n0 + i; ha = n0 + nS + i
        for y in G.lines[s]:
            E.append((hb, 1 * per + y)); E.append((ha, 2 * per + y))
        E.append((hb, ha))
    return n0 + 2 * nS, E, per, R

def check(G, S, M01, q, label):
    n, E, per, R = line_hub_edges(G, S, M01)
    deg = np.zeros(n, dtype=int)
    for a, b in E: deg[a] += 1; deg[b] += 1
    p = '/home/user/degree-diameter/research/squads/gqd5-r1/c8/tmp_lh_%s.txt' % label
    write(p, n, E)
    out = subprocess.run([APSP, p, str(q + 2), '5'], capture_output=True, text=True).stdout.strip().splitlines()[-1]
    dn, dg = diam_numpy(n, E)
    return out, 'numpy diam', dn, 'maxdeg', int(deg.max()), '|S|', len(S), '|R|', len(R)

if __name__ == '__main__':
    q = int(sys.argv[1]); G = getG(q); M = random_M01(G, 1)
    S = partial_spread(G, 0)
    print('max partial spread found', len(S))
    print('one line:', check(G, S[:1], M, q, 'one%d' % q))
    print('two lines:', check(G, S[:2], M, q, 'two%d' % q))
    print('max partial spread:', check(G, S, M, q, 'max%d' % q))
