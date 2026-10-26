# Build groups of order 208 = Z_13 x|_phi P, P over all 14 groups of order 16 (abelian ones by spec,
# nonabelian ones found by random search in S_8 plus explicit Q16 and Q8 x C2), phi: P -> Z_4 hom, Aut(Z_13) ~ Z_12.
import sys, random, itertools, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import groups as G

def inv_of(T):
    N = len(T)
    order = []
    for g in range(N):
        x, o = g, 1
        while x != 0:
            x = int(T[x, g]); o += 1
        order.append(o)
    cent = sum(1 for g in range(N) if (T[g] == T[:, g]).all())
    # derived subgroup
    invs = [int(np.where(T[g] == 0)[0][0]) for g in range(N)]
    comm = set(int(T[T[invs[g], invs[h]], T[g, h]]) for g in range(N) for h in range(N))
    S = {0}; frontier = [0]
    gens = list(comm)
    while frontier:
        nf = []
        for a in frontier:
            for b in gens:
                c = int(T[a, b])
                if c not in S: S.add(c); nf.append(c)
        frontier = nf
    sq = [0] * N
    for g in range(N): sq[int(T[g, g])] += 1
    cls = []
    seen = set()
    for a in range(N):
        if a in seen: continue
        c = set(int(T[T[g, a], invs[g]]) for g in range(N))
        seen |= c; cls.append(len(c))
    return (N, sorted(order).count(2), tuple(np.bincount(order).tolist()), cent, len(S),
            tuple(np.bincount(sq).tolist()), tuple(sorted(cls))), invs

def closure(gens, cap):
    e = tuple(range(8))
    S = {e}; fr = [e]
    while fr:
        nf = []
        for a in fr:
            for g in gens:
                c = tuple(g[i] for i in a)
                if c not in S:
                    S.add(c); nf.append(c)
                    if len(S) > cap: return None
        fr = nf
    return S

def perm_table(elems):
    idx = {e: i for i, e in enumerate(elems)}
    N = len(elems)
    T = np.empty((N, N), dtype=np.uint16)
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            T[i, j] = idx[tuple(a[k] for k in b)]
    return T

def to_identity0(T):
    N = len(T)
    e = [g for g in range(N) if (T[g] == np.arange(N)).all()][0]
    perm = [e] + [g for g in range(N) if g != e]
    # relabel so identity is index 0
    pos = {g: i for i, g in enumerate(perm)}
    T2 = np.empty_like(T)
    for i, g in enumerate(perm):
        for j, h in enumerate(perm):
            T2[i, j] = pos[int(T[g, h])]
    return T2

def custom_Q(n):
    # generalized quaternion of order 2n: a^n = 1 (a order n), b^2 = a^(n/2), b a b^-1 = a^-1
    els = [(i, j) for j in range(2) for i in range(n)]
    def mul(x, y):
        i, j = x; k, l = y
        e = i + (k if j == 0 else -k)
        jj = j + l
        if jj == 2: e += n // 2; jj = 0
        return (e % n, jj)
    idx = {e: t for t, e in enumerate(els)}
    N = len(els); T = np.empty((N, N), dtype=np.uint16)
    for a, x in enumerate(els):
        for b, y in enumerate(els):
            T[a, b] = idx[mul(x, y)]
    return T

def direct(TA, TB):
    return G.t_prod(TA, TB)

def homs_to_Z4(T):
    N = len(T)
    gens = []; H = {0}
    # greedy generators
    for g in range(1, N):
        if g not in H:
            gens.append(g)
            # closure
            H = {0}; fr = [0]
            while fr:
                nf = []
                for a in fr:
                    for s in gens:
                        c = int(T[a, s])
                        if c not in H: H.add(c); nf.append(c)
                fr = nf
            if len(H) == N: break
    res = set()
    for vals in itertools.product(range(4), repeat=len(gens)):
        f = {0: 0}; fr = [0]; ok = True
        while fr and ok:
            nf = []
            for a in fr:
                for s, v in zip(gens, vals):
                    c = int(T[a, s]); want = (f[a] + v) % 4
                    if c in f:
                        if f[c] != want: ok = False; break
                    else:
                        f[c] = want; nf.append(c)
                if not ok: break
            fr = nf
        if not ok or len(f) != N: continue
        if all(f[int(T[g, h])] == (f[g] + f[h]) % 4 for g in range(N) for h in range(N)):
            res.add(tuple(f[g] for g in range(N)))
    return res

def semi_13(TP, f):
    # Z_13 x|_psi P, psi(p) = 5^f(p) mod 13; element (x,p) index p + 16 x
    P = len(TP); M = 13
    psi = [pow(5, f[p], 13) for p in range(P)]
    N = P * M
    T = np.empty((N, N), dtype=np.uint16)
    for x in range(M):
        for p in range(P):
            a = p + P * x
            for y in range(M):
                for q in range(P):
                    b = q + P * y
                    c = int(TP[p, q]) + P * ((x + psi[p] * y) % M)
                    T[a, b] = c
    return T

if __name__ == '__main__':
    out = sys.argv[1]
    t0 = time.time()
    # nonabelian 16-groups from random S_8 search
    rng = random.Random(7)
    def rand_p2():
        while True:
            p = list(range(8)); rng.shuffle(p); p = tuple(p)
            o = 1; x = p
            ident = tuple(range(8))
            while x != ident:
                x = tuple(p[i] for i in x); o += 1
                if o > 8: break
            if o in (1, 2, 4, 8): return p
    P16 = {}
    for trial in range(6000):
        x = rand_p2(); y = rand_p2()
        S = closure([x, y], 16)
        if S is None or len(S) != 16: continue
        elems = sorted(S, key=lambda e: (e != tuple(range(8)), e))
        T = perm_table(elems)
        T = to_identity0(T)
        key, _ = inv_of(T)
        if key not in P16:
            P16[key] = T
        if len(P16) >= 9: break
    print('random S_8 16-groups found', len(P16), 'time', round(time.time() - t0, 1), file=sys.stderr)
    cands = list(P16.values())
    cands.append(custom_Q(8))
    cands.append(direct(custom_Q(4), G.table('cyc 2')))
    nonab = []
    seen = set()
    for T in cands:
        key, _ = inv_of(T)
        if key in seen: continue
        seen.add(key)
        if (T == T.T).all(): continue  # abelian check (table symmetric in commutative case)
        nonab.append(T)
    print('nonabelian order-16 groups', len(nonab), file=sys.stderr)
    # abelian P too (with nontrivial phi they give nonabelian G)
    absP = [G.table(s) for s in ['cyc 16', 'cyc 8 x cyc 2', 'cyc 4 x cyc 4', 'cyc 4 x cyc 2 x cyc 2', 'cyc 2 x cyc 2 x cyc 2 x cyc 2']]
    Ps = absP + nonab
    Gs = {}
    names = []
    for i, TP in enumerate(Ps):
        for f in homs_to_Z4(TP):
            if i < 5 and all(v == 0 for v in f) is False and False: pass
            T = semi_13(TP, list(f))
            key, invs = inv_of(T)
            if key in Gs: continue
            Gs[key] = T
            names.append((i, f))
    print('distinct groups of order 208 (by invariant):', len(Gs), file=sys.stderr)
    # write
    import pickle
    keys = list(Gs.keys())
    for idx, k in enumerate(keys):
        G.write_bin(Gs[k], f'{out}/g{idx:03d}.bin')
    print('written', len(keys), 'time', round(time.time() - t0, 1), file=sys.stderr)
    with open(f'{out}/index.txt', 'w') as fh:
        for idx, k in enumerate(keys):
            fh.write(f'g{idx:03d} order={k[0]} inv_sizes_class={sum(k[6])} centre={k[3]} derived={k[4]} involutions={k[1]}\n')
