"""c8: K22 starts with C chosen to put many flagged lines into W (best of CT random non-symplectic C's), see k22.py."""
import sys, random, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r5-d11D5/c8")
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *
import k22

def best_two(S, rng):
    S = sorted(S); cands = {}
    for i, a in enumerate(S):
        for b in S[i+1:]:
            if Bf(PTS[a], PTS[b]):
                h = frozenset(span(PTS[a], PTS[b]))
                cands[h] = len(h & set(S))
    items = sorted(cands.items(), key=lambda kv: -kv[1])
    if not items: return None, None
    H1 = items[0][0]
    for h, w in items[1:]:
        if not (h & H1): return sorted(H1), sorted(h)
    return None, None   # no disjoint second line: skip this C

if __name__ == "__main__":
    seed, out, CT = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
    rng = random.Random(seed)
    bestC = None
    for t in range(CT):
        while True:
            M = randmat(rng); C = pmap(M)
            if sum(is_W([C[p] for p in l[:2]]) for l in LINES) < n0: break
        S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
        h1, h2 = best_two(S, rng)
        if h1 is None or h2 is None: continue
        val = len(S & set(h1)) + len(S & set(h2))
        if bestC is None or val > bestC[0]: bestC = (val, M, C, S, h1, h2)
    print("best C value", bestC[0] if bestC else None, file=sys.stderr)
    if bestC: print("S-count on h1,h2:", len(bestC[3] & set(bestC[4])), len(bestC[3] & set(bestC[5])), file=sys.stderr)
