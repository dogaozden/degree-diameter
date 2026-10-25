"""Walk capacity per (side, base vertex i, base vertex t) for a base file, mirroring ctrl_search.c.
usage: python3 walkcount.py BASE FLAGS   (flags = chart flags file; prints min capacity vs |G| needs)"""
import sys
def read_base(path):
    lines = [l for l in open(path) if l.strip()]
    r = int(lines[0].split()[0]); E = []
    for l in lines[1:]:
        p = list(map(int, l.split()))
        if len(p) < 2: continue
        E.append((p[0], p[1], p[2] if len(p) == 3 else None))
    return r, E
def colour(r, E):
    ne = len(E); used = [False]*ne; col = [None]*ne
    EA = [e[0] for e in E]; EB = [e[1] for e in E]
    k = ne // r
    for c in range(k):
        matchB = [-1]*r
        def aug(a, visB):
            for e in range(ne):
                if not used[e] and EA[e] == a and not visB[EB[e]]:
                    visB[EB[e]] = True
                    if matchB[EB[e]] < 0 or aug(EA[matchB[EB[e]]], visB):
                        matchB[EB[e]] = e; return True
            return False
        for a in range(r):
            if not aug(a, [False]*r): raise SystemExit('colouring failed')
        for j in range(r):
            col[matchB[j]] = c; used[matchB[j]] = True
    return col
def read_flags(path, k):
    v = list(map(int, open(path).read().split()))
    kk = v[0]; assert kk == k
    p = 1
    sing = [v[p:p+k**4], v[p+k**4:p+2*k**4]]; p += 2*k**4
    pen = [v[p:p+k*k], v[p+k*k:p+2*k*k]]; p += 2*k*k
    diag = [v[p], v[p+1]]
    return sing, pen, diag
def capacity(r, E, flags, k):
    sing, pen, diag = flags
    col = colour(r, E); ne = len(E)
    EA = [e[0] for e in E]; EB = [e[1] for e in E]
    out = {}
    for s in range(2):
        X = EB if s else EA; Y = EA if s else EB
        for i in range(r):
            cnt = [0]*r; cnt2 = [0]*r
            for e1 in range(ne):
                if X[e1] != i: continue
                for e2 in range(ne):
                    if Y[e2] != Y[e1] or e2 == e1: continue
                    if pen[s][col[e1]*k + col[e2]]: cnt[X[e2]] += 1
                    for e3 in range(ne):
                        if e3 == e2 or X[e3] != X[e2]: continue
                        for e4 in range(ne):
                            if e4 == e3 or Y[e4] != Y[e3]: continue
                            idx = ((col[e1]*k + col[e2])*k + col[e3])*k + col[e4]
                            if sing[s][idx]: continue
                            cnt[X[e4]] += 1
            out[(s, i)] = cnt
    return out, col, diag
if __name__ == '__main__':
    base, flg = sys.argv[1], sys.argv[2]
    r, E = read_base(base); k = len(E)//r
    flags = read_flags(flg, k)
    out, col, diag = capacity(r, E, flags, k)
    print('base', base, 'r', r, 'k', k, 'colours', col, 'diag', diag)
    for key in sorted(out):
        print(' side', 'AB'[key[0]], 'vertex', key[1], 'capacity to each end', out[key])
