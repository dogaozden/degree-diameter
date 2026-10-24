"""Cayley tables of small groups for ctrl_search.c: python3 groups.py NAME out
NAME: cyc:n, dih:n (order 2n), dic:n (order 4n), prod:a:b (Z_a x Z_b), meta:m:n:t (Z_m x| Z_n, b a b^-1 = a^t),
q8, s3, a4, s4, a5, sl:p, psl:p, gl:p (2x2 over the prime field F_p)."""
import sys
def table_from(elems, op):
    idx = {e: i for i, e in enumerate(elems)}
    return [[idx[op(a, b)] for b in elems] for a in elems]
def close(gens, op, ident):
    S = [ident]; seen = {ident}; frontier = [ident]
    while frontier:
        nf = []
        for a in frontier:
            for g in gens:
                c = op(a, g)
                if c not in seen: seen.add(c); S.append(c); nf.append(c)
        frontier = nf
    return S
def perm_group(gens):
    n = len(gens[0]); ident = tuple(range(n))
    op = lambda a, b: tuple(a[b[i]] for i in range(n))
    return close(gens, op, ident), op
def mat_group(p, gens):
    op = lambda a, b: tuple(tuple(sum(a[i][t] * b[t][j] for t in range(2)) % p for j in range(2)) for i in range(2))
    return close(gens, op, ((1, 0), (0, 1))), op
def make(name):
    f = name.split(':')
    if f[0] == 'cyc':
        n = int(f[1]); return [[(a + b) % n for b in range(n)] for a in range(n)]
    if f[0] == 'prod':
        a_, b_ = int(f[1]), int(f[2]); E = [(x, y) for x in range(a_) for y in range(b_)]
        return table_from(E, lambda u, v: ((u[0] + v[0]) % a_, (u[1] + v[1]) % b_))
    if f[0] == 'meta':
        m, n, t = int(f[1]), int(f[2]), int(f[3]); assert pow(t, n, m) == 1 % m, 'need t^n = 1 mod m'
        E = [(x, y) for x in range(m) for y in range(n)]
        return table_from(E, lambda u, v: ((u[0] + pow(t, u[1], m) * v[0]) % m, (u[1] + v[1]) % n))
    if f[0] == 'dih':
        n = int(f[1]); return make('meta:%d:2:%d' % (n, n - 1))
    if f[0] == 'dic':
        n = int(f[1]); E = [(x, y) for x in range(2 * n) for y in range(2)]
        def op(u, v):
            a1, e1 = u; a2, e2 = v
            if e1 == 0: return ((a1 + a2) % (2 * n), e2)
            if e2 == 0: return ((a1 - a2) % (2 * n), 1)
            return ((a1 - a2 + n) % (2 * n), 0)
        return table_from(E, op)
    if f[0] == 'q8': return make('dic:2')
    if f[0] in ('s3', 'a4', 's4', 'a5'):
        gens = {'s3': [(1, 0, 2), (1, 2, 0)], 'a4': [(1, 2, 0, 3), (0, 2, 3, 1)], 's4': [(1, 0, 2, 3), (1, 2, 3, 0)],
                'a5': [(1, 2, 0, 3, 4), (0, 1, 3, 4, 2)]}[f[0]]
        E, op = perm_group(gens); return table_from(E, op)
    if f[0] in ('sl', 'gl', 'psl'):
        p = int(f[1])
        if f[0] == 'gl':
            E, op = mat_group(p, [((1, 1), (0, 1)), ((0, 1), (1, 0))] + [((g, 0), (0, 1)) for g in range(2, p)])
            return table_from(E, op)
        E, op = mat_group(p, [((1, 1), (0, 1)), ((0, p - 1), (1, 0))])
        if f[0] == 'sl': return table_from(E, op)
        neg = lambda a: tuple(tuple((-x) % p for x in row) for row in a)
        rep = lambda a: min(a, neg(a)); reps = sorted({rep(e) for e in E})
        return table_from(reps, lambda a, b: rep(op(a, b)))
    raise ValueError(name)
def check(T):
    n = len(T); e = next(i for i in range(n) if all(T[i][j] == j for j in range(n)))
    for a in range(n):
        assert sorted(T[a]) == list(range(n))
        for b in range(n):
            for c in range(n): assert T[T[a][b]][c] == T[a][T[b][c]]
    return n
if __name__ == '__main__':
    T = make(sys.argv[1]); n = check(T) if len(T) <= 60 else len(T)
    with open(sys.argv[2], 'w') as f:
        f.write('%d\n' % len(T)); f.write(' '.join(str(x) for row in T for x in row) + '\n')
    print(sys.argv[1], 'order', len(T))
