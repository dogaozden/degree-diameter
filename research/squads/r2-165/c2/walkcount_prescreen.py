# Group-independent necessary condition for mlift_chart cost 0.
# Each (source orbit, endpoint) pair needs >= n hitting walks (one per group element, n = 17 or 18), where hitting walks
# are non-backtracking length-2 walks plus non-backtracking length-4 walks with nonsingular colour pattern.
# Also each source orbit needs >= 1 closed nonsingular length-4 walk (the (i,e) target). Colours follow mlift_chart.c.
import sys, glob, os
R = '/home/user/degree-diameter/research/theorems/squad165'
def colour(k, EA, EB, ne):
    used = [False] * ne; col = [-1] * ne
    for c in range(4):
        matchB = [-1] * k; visB = [False] * k
        def aug(a):
            for e in range(ne):
                if not used[e] and EA[e] == a and not visB[EB[e]]:
                    visB[EB[e]] = True
                    if matchB[EB[e]] < 0 or aug(EA[matchB[EB[e]]]):
                        matchB[EB[e]] = e; return True
            return False
        for a in range(k):
            visB[:] = [False] * k
            assert aug(a), 'colouring failed'
        for j in range(k):
            col[matchB[j]] = c; used[matchB[j]] = True
    return col
def load_base(fn):
    L = open(fn).read().split(); k = int(L[0]); ne = 4 * k
    return k, ne, [int(L[1 + 2 * i]) for i in range(ne)], [int(L[2 + 2 * i]) for i in range(ne)]
def load_pat(fn):
    S = {'A': set(), 'B': set()}
    for line in open(fn):
        p = line.split()
        if len(p) == 6 and int(p[5]) < 4: S[p[0]].add(tuple(int(x) for x in p[1:5]))
    return S
def walks(k, ne, EA, EB, col, side):
    """list per orbit i: (endpoint, colourtuple or None for length 2, closed flag implicit)"""
    SA, SB = (EA, EB) if side == 'A' else (EB, EA)     # SA: vertex on the orbit side, SB: other side
    adjSA = [[e for e in range(ne) if SA[e] == v] for v in range(k)]
    adjSB = [[e for e in range(ne) if SB[e] == v] for v in range(k)]
    out = []
    for i in range(k):
        L = []
        for e1 in adjSA[i]:
            for e2 in adjSB[SB[e1]]:
                if e2 == e1: continue
                L.append((SA[e2], None))
                for e3 in adjSA[SA[e2]]:
                    if e3 == e2: continue
                    for e4 in adjSB[SB[e3]]:
                        if e4 == e3: continue
                        L.append((SA[e4], (col[e1], col[e2], col[e3], col[e4])))
        out.append(L)
    return out
if __name__ == '__main__':
    pats = sorted(os.path.basename(p) for p in glob.glob(R + '/charts/pat_c*_p*.txt'))
    P = {pf: load_pat(f'{R}/charts/{pf}') for pf in pats}
    for bi in range(26):
        k, ne, EA, EB = load_base(f'{R}/bases4/k4_{bi:03d}.txt'); col = colour(k, EA, EB, ne)
        W = {s: walks(k, ne, EA, EB, col, s) for s in 'AB'}
        res = []
        for pf in pats:
            mins = {}; low17 = low18 = 0; selfmin = 99
            for s in 'AB':
                cnt = [[0] * k for _ in range(k)]; closed = [0] * k
                for i in range(k):
                    for end, ct in W[s][i]:
                        if ct is not None and ct in P[pf][s]: continue
                        cnt[i][end] += 1
                        if ct is not None and end == i: closed[i] += 1
                mins[s] = min(min(r) for r in cnt)
                low17 += sum(x < 17 for r in cnt for x in r); low18 += sum(x < 18 for r in cnt for x in r)
                selfmin = min(selfmin, min(closed))
            res.append((pf, mins['A'], mins['B'], low17, low18, selfmin))
        best = max(res, key=lambda r: (r[3] == 0, r[4] == 0, -r[3], -r[4], r[5] > 0))
        ok17 = [r[0] for r in res if r[3] == 0 and r[5] > 0]; ok18 = [r[0] for r in res if r[4] == 0 and r[5] > 0]
        print(f'k4_{bi:03d} edges_dup={len(EA)-len(set(zip(EA,EB)))} minWA={min(r[1] for r in res)} minWB={min(r[2] for r in res)} '
              f'best={best[0]}(<17:{best[3]} <18:{best[4]} selfclosed={best[5]}) n17-feasible={len(ok17)} n18-feasible={len(ok18)}')
