"""mk_nl.py: base graphs for nlift (non-abelian voltage lifts of H(q) + a doubled matching), card c8 (r2_d14D8).

Groups (element index: identity = 0):
  Z{m}            cyclic
  D{k}            dihedral of order 2k, elements (s, e) = index 2s+e, (s1,e1)(s2,e2) = (s1 + (-1)^e1 s2, e1+e2)
  SD{k}_{L}_{c}   Z_k x| Z_L, generator t of Z_L acts on Z_k by multiplication by c (c^L = 1 mod k); index s*L+i
  S{n}            symmetric group S_n (n = 4 or 5), elements listed by BFS closure from the standard generators
Base graph (q prime): points 0..N-1 (side A) and lines 0..N-1 (side B); hexagon flags (p, l) carry voltage hexmode;
two parallel edges (p, phi(p)) with voltages u_p, w_p (u_p != w_p), phi a random permutation.
  hexmode: rand (uniform in G) | zero (identity) | normal (level-0 elements of SD: index multiple of L)
  phimode: rand (uniform, u != w) | lev (SD with L = 5 only: u = (a,1), w = (b,2), a, b uniform in Z_k)
Usage: python3 mk_nl.py q GROUP seed hexmode phimode OUTPREFIX     writes OUTPREFIX.grp and OUTPREFIX.base
"""
import sys, itertools
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load


def sd_table(k, L, c):
    assert pow(c, L, k) == 1 % k, 'c^L must be 1 mod k'
    m = k * L
    T = np.zeros((m, m), dtype=np.int64)
    for s1 in range(k):
        for i1 in range(L):
            cp = pow(c, i1, k)
            for s2 in range(k):
                for i2 in range(L):
                    T[s1 * L + i1, s2 * L + i2] = ((s1 + cp * s2) % k) * L + (i1 + i2) % L
    return T


def perm_table(gens, n):
    idp = tuple(range(n))
    elems = [idp]; index = {idp: 0}; q = [idp]
    while q:
        x = q.pop(0)
        for g in gens:
            y = tuple(g[x[i]] for i in range(n))  # y = g o x (apply x then g)
            if y not in index:
                index[y] = len(elems); elems.append(y); q.append(y)
    m = len(elems)
    T = np.zeros((m, m), dtype=np.int64)
    for i, x in enumerate(elems):
        for j, y in enumerate(elems):
            z = tuple(y[x[t]] for t in range(n))  # x*y = apply x then y
            T[i, j] = index[z]
    return T


def group(spec):
    if spec.startswith('SD'):
        k, L, c = (int(t) for t in spec[2:].split('_'))
        return sd_table(k, L, c), L
    if spec.startswith('D') and spec[1:].isdigit():
        k = int(spec[1:])
        return sd_table(k, 2, k - 1), 2
    if spec.startswith('Z') and spec[1:].isdigit():
        return sd_table(int(spec[1:]), 1, 1), 1
    if spec == 'S4':
        return perm_table([(1, 0, 2, 3), (1, 2, 3, 0)], 4), 1
    if spec == 'S5':
        return perm_table([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 5), 1
    raise SystemExit('unknown group ' + spec)


def check_group(T):
    m = T.shape[0]
    assert (T[0] == np.arange(m)).all() and (T[:, 0] == np.arange(m)).all()
    # associativity on random triples
    rng = np.random.default_rng(0)
    for _ in range(2000):
        x, y, z = rng.integers(0, m, 3)
        assert T[T[x, y], z] == T[x, T[y, z]]


if __name__ == '__main__':
    q, spec, seed = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
    hexmode, phimode, out = sys.argv[4], sys.argv[5], sys.argv[6]
    T, L = group(spec)
    m = T.shape[0]
    check_group(T)
    rng = np.random.default_rng(seed)
    N, LP, PL, coord = load(q)
    # hexagon flags
    ls = np.repeat(np.arange(N), q + 1); ps = LP.reshape(-1)
    if hexmode == 'zero':
        hv = np.zeros(len(ps), dtype=np.int64)
    elif hexmode == 'rand':
        hv = rng.integers(0, m, len(ps))
    elif hexmode == 'normal':
        assert L > 1
        hv = rng.integers(0, m // L, len(ps)) * L
    else:
        raise SystemExit('hexmode')
    E = [np.stack([ps, ls, hv], axis=1)]
    phi = rng.permutation(N)
    if phimode == 'rand':
        u = rng.integers(0, m, N); w = rng.integers(0, m, N)
        bad = u == w
        while bad.any():
            w[bad] = rng.integers(0, m, bad.sum()); bad = u == w
    elif phimode == 'lev':
        assert L == 5
        k = m // L
        u = rng.integers(0, k, N) * L + 1
        w = rng.integers(0, k, N) * L + 2
    else:
        raise SystemExit('phimode')
    E.append(np.stack([np.arange(N), phi, u], axis=1))
    E.append(np.stack([np.arange(N), phi, w], axis=1))
    edges = np.concatenate(E)
    with open(out + '.grp', 'w') as f:
        f.write(f'{m}\n')
        np.savetxt(f, T.reshape(1, -1), fmt='%d')
    with open(out + '.base', 'w') as f:
        f.write(f'{N} {N}\n')
        np.savetxt(f, edges, fmt='%d')
    print(f'q={q} group {spec} order {m} hex={hexmode} phi={phimode} edges={len(edges)} -> {out}.grp {out}.base')
