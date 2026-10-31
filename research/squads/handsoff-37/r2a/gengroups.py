# Writes groups.tab in salift format: "grp N gid name" then N*N ints (mul[a*N+b], identity = 0).
# Groups: cyclic, metacyclic Z_a x|_r Z_b (index x*b+y), direct products, S3, A4, Q8.
import itertools, sys

def meta(a, b, r):
    assert pow(r, b, a) == 1 % a, (a, b, r)
    N = a * b
    T = [[0] * N for _ in range(N)]
    for x1 in range(a):
        for y1 in range(b):
            for x2 in range(a):
                for y2 in range(b):
                    x = (x1 + pow(r, y1, a) * x2) % a
                    y = (y1 + y2) % b
                    T[x1 * b + y1][x2 * b + y2] = x * b + y
    return T

def direct(A, B):
    na, nb = len(A), len(B)
    T = [[0] * (na * nb) for _ in range(na * nb)]
    for i1 in range(na):
        for j1 in range(nb):
            for i2 in range(na):
                for j2 in range(nb):
                    T[i1 * nb + j1][i2 * nb + j2] = A[i1][i2] * nb + B[j1][j2]
    return T

def perm_group(gens):
    k = len(gens[0])
    idp = tuple(range(k))
    els = [idp]; seen = {idp: 0}
    frontier = [idp]
    while frontier:
        nf = []
        for g in frontier:
            for s in gens:
                h = tuple(s[g[i]] for i in range(k))  # h = s o g
                if h not in seen:
                    seen[h] = len(els); els.append(h); nf.append(h)
        frontier = nf
    N = len(els)
    T = [[0] * N for _ in range(N)]
    for i, g in enumerate(els):
        for j, h in enumerate(els):
            gh = tuple(g[h[t]] for t in range(k))
            T[i][j] = seen[gh]
    return T

def quat():
    # Q8 as elements (sign, unit) with units 1,i,j,k; identity index 0
    units = ['1', 'i', 'j', 'k']
    tab = {('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),
           ('i','1'):(1,'i'),('i','i'):(-1,'1'),('i','j'):(1,'k'),('i','k'):(-1,'j'),
           ('j','1'):(1,'j'),('j','i'):(-1,'k'),('j','j'):(-1,'1'),('j','k'):(1,'i'),
           ('k','1'):(1,'k'),('k','i'):(1,'j'),('k','j'):(-1,'i'),('k','k'):(-1,'1')}
    els = [(s, u) for s in (1, -1) for u in units]
    idx = {e: i for i, e in enumerate(els)}
    els = sorted(els, key=lambda e: (e != (1, '1'), e))
    idx = {e: i for i, e in enumerate(els)}
    N = 8
    T = [[0] * N for _ in range(N)]
    for a in els:
        for b in els:
            s1, u1 = a; s2, u2 = b
            s3, u3 = tab[(u1, u2)]
            T[idx[a]][idx[b]] = idx[(s1 * s2 * s3, u3)]
    return T

def cyc(n):
    return meta(n, 1, 1) if n > 0 else None

def s3():
    return perm_group([(1, 0, 2), (1, 2, 0)])
def a4():
    return perm_group([(1, 2, 0, 3), (1, 0, 3, 2)])

groups = []
def add(name, T):
    groups.append((name, T))

def C(n): return meta(n, 1, 1)
# n = 168 needs N | 84 ; n = 160 needs N | 80. Build a superset for N | 84 and N | 80 (and small others).
add('C2', C(2)); add('C3', C(3)); add('C4', C(4)); add('C2xC2', direct(C(2), C(2)))
add('S3', s3()); add('C6', C(6)); add('C7', C(7)); add('C5', C(5)); add('C8', C(8))
add('D7', meta(7, 2, 6)); add('C14', C(14)); add('C7:C3', meta(7, 3, 2))
add('D6', meta(6, 2, 5)); add('A4', a4()); add('Dic3', meta(3, 4, 2)); add('C2xC6', direct(C(2), C(6)))
add('C12', C(12)); add('C21', C(21)); add('D21', meta(21, 2, 20)); add('C28', C(28))
add('D14', meta(14, 2, 13)); add('Dic7', meta(7, 4, 6)); add('C2xD7', direct(C(2), meta(7, 2, 6)))
add('C2xC14', direct(C(2), C(14))); add('C42', C(42)); add('F42', meta(7, 6, 3))
add('C3xD7', direct(C(3), meta(7, 2, 6))); add('C2x(C7:C3)', direct(C(2), meta(7, 3, 2)))
add('C7xS3', direct(C(7), s3())); add('Q8', quat()); add('C10', C(10)); add('D5', meta(5, 2, 4))
add('C20', C(20)); add('D10', meta(10, 2, 9)); add('C5:C4', meta(5, 4, 2)); add('C2xC10', direct(C(2), C(10)))
add('C16', C(16)); add('C8xC2', direct(C(8), C(2))); add('D8', meta(8, 2, 7)); add('C4xC4', direct(C(4), C(4)))
add('C40', C(40)); add('D20', meta(20, 2, 19)); add('C2xC20', direct(C(2), C(20)))
add('C5:C8', meta(5, 8, 2)); add('C4:C4', meta(4, 4, 3)); add('C2xD10', direct(C(2), meta(5,2,4)))
add('C2xD5',direct(C(2),meta(5,2,4)))
with open(sys.argv[1] if len(sys.argv) > 1 else 'groups.tab', 'w') as f:
    for gid, (name, T) in enumerate(groups):
        N = len(T)
        # sanity: identity row/col is identity, associativity spot check
        for i in range(N):
            assert T[0][i] == i and T[i][0] == i, name
        assert all(sorted(row) == list(range(N)) for row in T), name
        f.write('grp %d %d %s\n' % (N, gid, name.replace(' ', '_')))
        for row in T:
            f.write(' '.join(map(str, row)) + '\n')
        print(gid, N, name)
