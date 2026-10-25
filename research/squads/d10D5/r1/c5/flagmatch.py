"""flagmatch.py: can sigma be chosen so that k freed flags (p_i in l_i = sigma(p_i)) all have exact coverage?
Allowed (x, M): for every i, M in G_i (lines meeting l_i, not through p_i) => x in p_i^perp \\ {p_i}, and
x in A_i (points collinear with p_i, not on l_i) => M in l_i^perp \\ {l_i}; freed points/lines excluded; p_i <-> l_i.
Reports the maximum matching size (N = perfect)."""
import sys, random
sys.path.insert(0, '.')
from gq import load, perp, lperp

def hk(adjL, nL, nR):
    """Hopcroft-Karp (simple augmenting-path version is enough at N = 400)"""
    matchR = [-1] * nR; matchL = [-1] * nL
    def try_(u, seen):
        for v in adjL[u]:
            if v in seen: continue
            seen.add(v)
            if matchR[v] < 0 or try_(matchR[v], seen):
                matchR[v] = u; matchL[u] = v; return True
        return False
    sys.setrecursionlimit(10000)
    size = 0
    for u in range(nL):
        if try_(u, set()): size += 1
    return size, matchL

def setup(q, N, lines, lof, flags):
    P = [perp(lines, lof, p) for p in range(N)]
    Lp = [lperp(lines, lof, l) for l in range(N)]
    F = {p for p, l in flags}; Fl = {l for p, l in flags}
    A = [P[p] - set(lines[l]) for p, l in flags]
    G = [Lp[l] - set(lof[p]) for p, l in flags]
    Pp = [P[p] - {p} for p, l in flags]
    Ll = [Lp[l] - {l} for p, l in flags]
    adj = []
    for x in range(N):
        if x in F:
            adj.append([dict(flags)[x]]); continue
        Ix = [i for i in range(len(flags)) if x in A[i]]
        row = []
        for M in range(N):
            if M in Fl: continue
            ok = all(M in Ll[i] for i in Ix) and all(x in Pp[i] for i in range(len(flags)) if M in G[i])
            if ok: row.append(M)
        adj.append(row)
    return adj

if __name__ == '__main__':
    q, N, lines, lof = load(sys.argv[1]); k = int(sys.argv[2]); seed = int(sys.argv[3]); mode = sys.argv[4] if len(sys.argv) > 4 else 'far'
    rng = random.Random(seed)
    P = [perp(lines, lof, p) for p in range(N)]
    flags = []
    for p in rng.sample(range(N), N):
        if len(flags) == k: break
        if mode == 'far' and any(p in P[f] for f, _ in flags): continue
        cand = [l for l in lof[p] if mode != 'far' or all(not (set(lines[l]) & set(lines[g])) for _, g in flags)]
        if not cand: continue
        flags.append((p, rng.choice(cand)))
    adj = setup(q, N, lines, lof, flags)
    size, mL = hk(adj, N, N)
    print('k', len(flags), 'flags', flags, 'matching', size, 'of', N)
