"""Necessary-condition filter (c2): for base B and flags, count valid walks N_s(i,w) exactly as ctrl_search.c builds them.
Cost 0 needs N_s(i,w) + [w==i]*diag_s >= |G| for every side s, base vertex i, base vertex w.
usage: python3 walkcount.py BASE FLAGS  -> prints min over (s,i,w) of N + diag, and the per-side minima."""
import sys
def read_base(path):
    rows = [l.split() for l in open(path) if l.strip()]
    r = int(rows[0][0]); EA = []; EB = []; col = []; given = True
    for x in rows[1:]:
        if len(x) < 2: continue
        EA.append(int(x[0])); EB.append(int(x[1]))
        if len(x) == 3: col.append(int(x[2]))
        else: given = False
    ne = len(EA); k = ne // r
    if not given:
        col = [-1] * ne; used = [False] * ne
        for c in range(k):
            matchB = [-1] * r
            def aug(a, visB):
                for e in range(ne):
                    if not used[e] and EA[e] == a and not visB[EB[e]]:
                        visB[EB[e]] = True
                        if matchB[EB[e]] < 0 or aug(EA[matchB[EB[e]]], visB):
                            matchB[EB[e]] = e; return True
                return False
            for a in range(r):
                if not aug(a, [False] * r): raise SystemExit('colouring failed')
            for j in range(r):
                col[matchB[j]] = c; used[matchB[j]] = True
    return r, k, ne, EA, EB, col
def read_flags(path, k):
    v = [int(x) for x in open(path).read().split()]
    p = 0; kk = v[p]; p += 1; assert kk == k
    sing = {}
    for s in (0, 1):
        for a in range(k):
            for b in range(k):
                for c in range(k):
                    for d in range(k):
                        sing[(s, a, b, c, d)] = v[p]; p += 1
    pen = {}
    for s in (0, 1):
        for a in range(k):
            for b in range(k):
                pen[(s, a, b)] = v[p]; p += 1
    diag = [v[p], v[p + 1]]
    return sing, pen, diag
def counts(base, flags):
    r, k, ne, EA, EB, col = read_base(base)
    sing, pen, diag = read_flags(flags, k)
    N = {}
    for s in (0, 1):
        X = EA if s == 0 else EB; Y = EB if s == 0 else EA
        for i in range(r):
            for w in range(r): N[(s, i, w)] = 0
            for e1 in range(ne):
                if X[e1] != i: continue
                for e2 in range(ne):
                    if Y[e2] != Y[e1] or e2 == e1: continue
                    if pen[(s, col[e1], col[e2])]: N[(s, i, X[e2])] += 1
                    for e3 in range(ne):
                        if e3 == e2 or X[e3] != X[e2]: continue
                        for e4 in range(ne):
                            if e4 == e3 or Y[e4] != Y[e3]: continue
                            if sing[(s, col[e1], col[e2], col[e3], col[e4])]: continue
                            N[(s, i, X[e4])] += 1
    return r, k, N, diag
if __name__ == '__main__':
    base, flags = sys.argv[1], sys.argv[2]
    r, k, N, diag = counts(base, flags)
    best = {}
    for s in (0, 1):
        mins = []
        for i in range(r):
            for w in range(r):
                val = N[(s, i, w)] + (diag[s] if w == i else 0)
                mins.append(val)
        best[s] = min(mins)
    print('side A min %d side B min %d -> max |G| bound %d' % (best[0], best[1], min(best[0], best[1])))
    print('  N_A', [[N[(0, i, w)] for w in range(r)] for i in range(r)], 'N_B', [[N[(1, i, w)] for w in range(r)] for i in range(r)], 'diag', diag)
