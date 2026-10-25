"""c7 generator: permutation-voltage lifts of H(q) + extra matchings (read-only use of the cell's hex/hex_q{q}.bin).

Families (fibre = {0..m-1}, every base edge carries one permutation of the fibre):
  Z    : cyclic group Z_m acting by translation (regular)           -- control, same as cyclic voltages
  D    : dihedral group of order m (m even) acting by right multiplication (regular, non-abelian)
  H27  : Heisenberg group of order 27 (m = 27), right multiplication (regular, non-abelian)
  AFF  : affine maps x -> a x + b on Z_p (m = p prime), all a in Z_p^*, b in Z_p (non-regular)
hexmode: zero (identity on hexagon edges) | rand (uniform random group/affine element)
Usage: python3 gen.py q family m seed hexmode nmatch out.txt [--structured]
Writes "nA nB m P", P permutation lines, then "a b pid" edge lines (A = points, B = lines).
"""
import sys
import numpy as np


def load_hex(q):
    fn = f'/home/user/degree-diameter/research/squads/cells/d14D8_work/hex/hex_q{q}.bin'
    raw = np.fromfile(fn, dtype=np.int32, count=3)
    qq, N, L = (int(x) for x in raw)
    LP = np.fromfile(fn, dtype=np.int32, count=3 + L * (q + 1))[3:].reshape(L, q + 1)
    return N, LP


def group_table(fam, m):
    """Return (P, table) where table[g][x] = x * g (right multiplication) and identity index 0."""
    if fam == 'Z':
        return np.array([[(x + g) % m for x in range(m)] for g in range(m)])
    if fam == 'D':
        n = m // 2
        el = [(t, i) for t in range(2) for i in range(n)]
        idx = {e: j for j, e in enumerate(el)}
        def mul(x, y):
            t1, i1 = x; t2, i2 = y
            return ((t1 + t2) % 2, ((i1 * (1 if t2 == 0 else -1)) + i2) % n)
        return np.array([[idx[mul(el[x], el[g])] for x in range(m)] for g in range(m)])
    if fam == 'H27':
        el = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
        idx = {e: j for j, e in enumerate(el)}
        def mul(x, y):
            a1, b1, c1 = x; a2, b2, c2 = y
            return ((a1 + a2) % 3, (b1 + b2) % 3, (c1 + c2 + a1 * b2) % 3)
        return np.array([[idx[mul(el[x], el[g])] for x in range(m)] for g in range(m)])
    raise ValueError(fam)


def affine_table(p):
    """All maps x -> a x + b on Z_p with a != 0; index 0 is the identity (a=1,b=0)."""
    maps = [(1, 0)] + [(a, b) for a in range(1, p) for b in range(p) if not (a == 1 and b == 0)]
    tab = np.array([[(a * x + b) % p for x in range(p)] for (a, b) in maps])
    return maps, tab


def matching(N, rng, inc_pl):
    """random bijection points -> lines with M(x) not incident to x and M_j(x) != earlier matchings (fixed by swaps)."""
    M = rng.permutation(N)
    return M


def fix_matchings(Ms, N, rng, PL):
    """Repair: no M_j(x) incident to x, and no two matchings agree at x (swap images among points)."""
    incident = [set(PL[x].tolist()) for x in range(N)]
    for it in range(10 ** 7):
        bad = None
        for j, M in enumerate(Ms):
            for x in range(N):
                if M[x] in incident[x]:
                    bad = (j, x); break
            if bad: break
        if bad is None:
            for x in range(N):
                for j in range(len(Ms)):
                    for jj in range(j):
                        if Ms[j][x] == Ms[jj][x]:
                            bad = (j, x); break
                    if bad: break
                if bad: break
        if bad is None:
            return Ms
        j, x = bad
        y = int(rng.integers(N))
        Ms[j][x], Ms[j][y] = Ms[j][y], Ms[j][x]
    raise RuntimeError('matching repair failed')


def build(q, fam, m, seed, hexmode, nmatch):
    rng = np.random.default_rng(seed)
    N, LP = load_hex(q)
    L = LP.shape[0]
    PL = np.zeros((N, q + 1), dtype=np.int64)
    cnt = np.zeros(N, dtype=np.int64)
    for l in range(L):
        for p in LP[l]:
            PL[p, cnt[p]] = l
            cnt[p] += 1
    if fam == 'AFF':
        maps, tab = affine_table(m)
        P, table = len(maps), tab
        identity = 0
    else:
        table = group_table(fam, m)
        P = m
        identity = 0
    # base edges
    hex_p = LP.reshape(-1).astype(np.int64)
    hex_l = np.repeat(np.arange(L), q + 1).astype(np.int64)
    edges_a, edges_b, edges_pid = [], [], []
    hpid = np.zeros(len(hex_p), dtype=np.int64) if hexmode == 'zero' else rng.integers(0, P, len(hex_p))
    if hexmode == 'zero':
        hpid[:] = identity
    edges_a.append(hex_p); edges_b.append(hex_l); edges_pid.append(hpid)
    Ms = [rng.permutation(N) for _ in range(nmatch)]
    Ms = fix_matchings(Ms, N, rng, PL)
    for M in Ms:
        edges_a.append(np.arange(N)); edges_b.append(M.astype(np.int64))
        edges_pid.append(rng.integers(0, P, N))
    ea = np.concatenate(edges_a); eb = np.concatenate(edges_b); ep = np.concatenate(edges_pid)
    return N, P, table, ea, eb, ep, L


def write(out, N, P, table, ea, eb, ep, m):
    with open(out, 'w') as f:
        f.write(f'{N} {N} {m} {P}\n')
        for row in table:
            f.write(' '.join(str(int(v)) for v in row) + '\n')
        np.savetxt(f, np.stack([ea, eb, ep], axis=1), fmt='%d')


if __name__ == '__main__':
    q, fam, m, seed = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    hexmode, nmatch, out = sys.argv[5], int(sys.argv[6]), sys.argv[7]
    N, P, table, ea, eb, ep, L = build(q, fam, m, seed, hexmode, nmatch)
    assert table.shape == (P, m), (table.shape, P, m)
    write(out, N, P, table, ea, eb, ep, m)
    print(f'wrote {out}: N={N} edges={len(ea)} P={P} m={m} deg_A={q+1+nmatch} lift_vertices={2*N*m}')
