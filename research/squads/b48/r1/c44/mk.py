# Builds group tables for Z_m x| Q (Q non-cyclic small group), phi: Q -> Z_m^* given by images of 2 generators.
# Element (t,q) has index qi*m + t (identity = index 0); (t,q)(t',q') = (t + phi(q) t', q q').
# Writes .bin in groups.py format: int32 N, then N*N uint16 row-major.
import sys, itertools, numpy as np
from math import gcd

def closure(gens, mul, ident):
    elems = [ident]; idx = {ident: 0}; i = 0
    while i < len(elems):
        x = elems[i]; i += 1
        for g in gens:
            y = mul(x, g)
            if y not in idx:
                idx[y] = len(elems); elems.append(y)
    T = np.array([[idx[mul(x, y)] for y in elems] for x in elems], dtype=np.int64)
    return elems, idx, T

def perm_mul(p, q):  # (p*q)(i) = q(p(i))  -- any consistent convention works
    return tuple(q[i] for i in p)

def small_groups():
    G = {}
    # S3 and D4 and A4 as permutation groups
    s3 = (lambda: (1, 0, 2), )
    S3 = closure([(1, 0, 2), (1, 2, 0)], perm_mul, (0, 1, 2))
    G['S3'] = (S3[2], [1, 2])  # generator indices into elements list: we pick by value below
    D4 = closure([(1, 2, 3, 0), (0, 3, 2, 1)], perm_mul, (0, 1, 2, 3))
    G['D4'] = (D4[2], None)
    A4 = closure([(1, 2, 0, 3), (1, 0, 3, 2)], perm_mul, (0, 1, 2, 3))
    G['A4'] = (A4[2], None)
    # Q8 as signed units (sign, unit) with unit in {1,i,j,k}
    def qmul(a, b):
        s1, u1 = a; s2, u2 = b
        tbl = {(0,0):(1,0),(0,1):(1,1),(0,2):(1,2),(0,3):(1,3),
               (1,0):(1,1),(1,1):(-1,0),(1,2):(1,3),(1,3):(-1,2),
               (2,0):(1,2),(2,1):(-1,3),(2,2):(-1,0),(2,3):(1,1),
               (3,0):(1,3),(3,1):(1,2),(3,2):(-1,1),(3,3):(-1,0)}
        s3, u3 = tbl[(u1, u2)]
        return (s1 * s2 * s3, u3)
    Q8 = closure([(1, 1), (1, 2)], qmul, (1, 0))
    G['Q8'] = (Q8[2], None)
    return G

def abel_group(a, b):
    elems = [(i, j) for i in range(a) for j in range(b)]
    idx = {e: k for k, e in enumerate(elems)}
    T = np.array([[idx[((x[0] + y[0]) % a, (x[1] + y[1]) % b)] for y in elems] for x in elems], dtype=np.int64)
    return T, [idx[(1 % a, 0)], idx[(0, 1 % b)]]

def build_Q(name):
    if name.startswith('Z'):
        a, b = map(int, name[1:].split('x'))
        return abel_group(a, b)
    G = small_groups()
    T, _ = G[name]
    return T, None

def find_gens(T):
    n = T.shape[0]
    # greedy: pick pairs generating whole group
    for a in range(1, n):
        for b in range(a, n):
            S = {0}; frontier = [0]
            gens = [a, b]
            seen = {0}; st = [0]
            while st:
                x = st.pop()
                for g in gens:
                    y = T[x, g]
                    if y not in seen:
                        seen.add(y); st.append(y)
            if len(seen) == n:
                return gens
    raise RuntimeError('no 2 gens')

def homs(m, T, gens):
    n = T.shape[0]
    units = [u for u in range(1, m) if gcd(u, m) == 1]
    out = set()
    for u1, u2 in itertools.product(units, repeat=2):
        phi = [-1] * n; phi[0] = 1; st = [0]; ok = True
        val = {gens[0]: u1, gens[1]: u2}
        while st and ok:
            x = st.pop()
            for g in gens:
                y = T[x, g]; v = phi[x] * val[g] % m
                if phi[y] == -1:
                    phi[y] = v; st.append(y)
                elif phi[y] != v:
                    ok = False; break
        if ok and all(p != -1 for p in phi):
            out.add(tuple(phi))
    return out

def semidirect(m, QT, phi):
    n = QT.shape[0]
    phi = np.array(phi, dtype=np.int64)
    N = m * n
    # index = qi*m + t
    qi = np.repeat(np.arange(n), m)   # for index k: qi = k // m
    t = np.tile(np.arange(m), n)      # t = k % m
    A_q = qi[:, None]; B_q = qi[None, :]
    A_t = t[:, None]; B_t = t[None, :]
    newt = (A_t + phi[A_q] * B_t) % m
    newq = QT[A_q, B_q]
    return (newq * m + newt).astype(np.int64)

def check_group(T, trials=3000, rng=np.random.default_rng(1)):
    n = T.shape[0]
    for _ in range(trials):
        a, b, c = rng.integers(0, n, 3)
        assert T[T[a, b], c] == T[a, T[b, c]]
    assert (T[0] == np.arange(n)).all() and (T[:, 0] == np.arange(n)).all()

def write_bin(T, path):
    N = T.shape[0]
    with open(path, 'wb') as f:
        np.array([N], dtype=np.int32).tofile(f)
        T.astype(np.uint16).tofile(f)

if __name__ == '__main__':
    # usage: mk.py Q m OUTPREFIX [index_of_hom]   -> lists homs, or writes the chosen one
    Qname, m, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    QT, _ = build_Q(Qname)
    gens = find_gens(QT)
    H = sorted(homs(m, QT, gens))
    print(f'Q={Qname} |Q|={QT.shape[0]} m={m} N={m*QT.shape[0]} gens={gens} homs={len(H)}')
    if len(sys.argv) > 4:
        k = int(sys.argv[4]); phi = H[k]
        print('phi', phi[:16], 'phi-gens', [phi[g] for g in gens])
        T = semidirect(m, QT, phi)
        check_group(T)
        write_bin(T, out)
        print('wrote', out, T.shape[0])
