# a15 sweep: exhaustive cubic Haar (exh3, S={e,x,y}) over non-metacyclic groups of order 1185..1700.
import sys, os, subprocess, time, math
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import groups
HERE = '/home/user/degree-diameter/research/squads/raise-d12/r1/a15'
EXH = '/home/user/degree-diameter/research/squads/raise-d12/bin/exh3'
LO, HI, D = 1185, 1700, 12
LOG = os.path.join(HERE, 'sweep_log.txt')
TMP = os.path.join(HERE, 'tables')
os.makedirs(TMP, exist_ok=True)

def log(s):
    with open(LOG, 'a') as f:
        f.write(s + '\n')

def mat_key(M, p):
    a, b, c, d = M
    return ((a + d) % p, (a * d - b * c) % p, bool(b % p == 0 and c % p == 0 and (a - d) % p == 0))

def mat_mul(X, Y, p):
    a, b, c, d = X; e, f, g, h = Y
    return ((a*e + b*g) % p, (a*f + b*h) % p, (c*e + d*g) % p, (c*f + d*h) % p)

def mat_pow(M, k, p):
    R = (1, 0, 0, 1)
    for _ in range(k):
        R = mat_mul(R, M, p)
    return R

def semi_reps(p, k):
    """conjugacy-class reps M of GL(2,p) with M^k = I, deduplicated under M -> M^j (gcd(j,k)=1)."""
    reps = {}
    for a in range(p):
        for b in range(p):
            for c in range(p):
                for d in range(p):
                    if (a * d - b * c) % p == 0:
                        continue
                    kk = mat_key((a, b, c, d), p)
                    if kk not in reps:
                        reps[kk] = (a, b, c, d)
    out = []
    for kk, M in reps.items():
        if mat_pow(M, k, p) != (1, 0, 0, 1):
            continue
        orb = []
        for j in range(1, k + 1):
            if math.gcd(j, k) == 1:
                orb.append(mat_key(mat_pow(M, j, p), p))
        if kk == min(orb):
            out.append(M)
    return out

def t_dicyclic(n):
    """Dic_n of order 4n: a^i b^j, a^{2n}=1, b^2=a^n, b a b^-1 = a^-1."""
    m = 2 * n
    els = [(i, j) for j in range(2) for i in range(m)]
    idx = {e: t for t, e in enumerate(els)}
    N = len(els)
    T = np.empty((N, N), dtype=np.uint16)
    for x, (i, j) in enumerate(els):
        for y, (k, l) in enumerate(els):
            sgn = 1 if j == 0 else -1
            ii = (i + sgn * k) % m
            jj = j + l
            if jj == 2:
                ii = (ii + n) % m
                jj = 0
            T[x, y] = idx[(ii, jj)]
    return T

def t_gendihedral(a, b):
    """Dih(Z_a x Z_b) = (Z_a x Z_b) x| Z_2 with inversion; order 2ab."""
    els = [(x, y, s) for s in range(2) for x in range(a) for y in range(b)]
    idx = {e: t for t, e in enumerate(els)}
    N = len(els)
    T = np.empty((N, N), dtype=np.uint16)
    for u, (x, y, s) in enumerate(els):
        for v, (z, w, t) in enumerate(els):
            sg = 1 if s == 0 else -1
            T[u, v] = idx[((x + sg * z) % a, (y + sg * w) % b, (s + t) % 2)]
    return T

def build(spec):
    if spec[0] == 'dicyclic':
        return t_dicyclic(spec[1])
    if spec[0] == 'gendih':
        return t_gendihedral(spec[1], spec[2])
    if spec[0] == 'semi':
        _, p, k, M = spec
        return groups.table('semi %d %d %d %d %d %d' % (p, k, M[0], M[1], M[2], M[3]))
    return cached_spec(spec[1])

_CACHE = {}
def cached_table(part):
    if part not in _CACHE:
        _CACHE[part] = groups.table(part)
    return _CACHE[part]

def cached_spec(s):
    if ' x ' in s:
        parts = s.split(' x ')
        T = cached_table(parts[0])
        for q in parts[1:]:
            T = groups.t_prod(T, cached_table(q))
        return T
    return cached_table(s)

def run(name, spec, N_expect=None):
    t0 = time.time()
    try:
        T = build(spec)
    except Exception as e:
        log(f'{name} BUILD_ERROR {e}')
        return None
    N = len(T)
    fn = os.path.join(TMP, 'g.bin')
    groups.write_bin(T, fn)
    del T
    prefix = os.path.join(HERE, 'hit_' + name.replace(' ', '_').replace('/', '_'))
    try:
        out = subprocess.run(['timeout', '100', 'nice', '-n', '10', EXH, fn, str(D), prefix],
                             capture_output=True, text=True, env=dict(os.environ, THREADS='1', OMP_NUM_THREADS='1')).stdout
    except Exception as e:
        out = 'EXH_ERROR ' + str(e)
    os.remove(fn)
    gl = [l for l in out.splitlines() if l.startswith('GROUP')]
    res = 'FOUND' if 'RESULT FOUND' in out else ('NONE' if 'RESULT NONE' in out else 'TIMEOUT_OR_ERR')
    info = gl[0] if gl else out[-200:].replace('\n', ' | ')
    log(f'{name} | N={N} 2N={2*N} | {res} | {info} | build+run {time.time()-t0:.1f}s')
    if res == 'FOUND':
        log(f'!!! FOUND {name} N={N}')
    return res

if __name__ == '__main__':
    part = sys.argv[1]
    jobs = []
    if part == 'semi':
        for p in [7, 11, 13, 5, 17, 19, 23, 29]:
            for k in range(2, 80):
                if not (LO <= p * p * k <= HI):
                    continue
                for M in semi_reps(p, k):
                    if M == (1, 0, 0, 1) or (M[1] == 0 and M[2] == 0 and M[0] == M[3]):
                        continue  # abelian or scalar action: exh3 cost ~ classes x N, no value
                    jobs.append((f'semi_p{p}_k{k}_M{M[0]}_{M[1]}_{M[2]}_{M[3]}', ('semi', p, k, M)))
    elif part == 'prod':
        specs = ['psl2 11 x cyc 2', 'pgl2 11', 'sl2 5 x cyc 10', 'sl2 5 x cyc 11', 'sl2 5 x cyc 12', 'sl2 5 x cyc 13',
                 'sl2 5 x cyc 14', 'psl2 5 x cyc 20', 'psl2 5 x cyc 21', 'psl2 5 x cyc 22', 'psl2 5 x cyc 23', 'psl2 5 x cyc 24',
                 'psl2 5 x cyc 25', 'psl2 5 x cyc 26', 'psl2 5 x cyc 27', 'psl2 5 x cyc 28',
                 'psl2 7 x cyc 8', 'psl2 7 x cyc 9', 'psl2 7 x cyc 10', 'pgl2 7 x cyc 4', 'pgl2 7 x cyc 5',
                 'sl2 7 x cyc 4', 'sl2 7 x cyc 5', 'psl2 5 x dih 10', 'psl2 5 x dih 11', 'psl2 5 x dih 12',
                 'psl2 5 x dih 13', 'psl2 5 x dih 14', 'psl2 7 x dih 4', 'psl2 7 x dih 5',
                 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x cyc 10', 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x cyc 11',
                 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x cyc 12', 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x cyc 13',
                 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x cyc 14', 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x dih 10',
                 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x dih 11', 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x dih 12',
                 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x dih 13', 'perm 5 1,2,0,3,4 ; 1,2,3,4,0 x dih 14',
                 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 50', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 52', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 54',
                 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 56', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 58', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 60',
                 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 62', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 64', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 66',
                 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 68', 'perm 4 1,0,2,3 ; 1,2,3,0 x cyc 70',
                 'perm 4 1,0,2,3 ; 1,2,3,0 x dih 25', 'perm 4 1,0,2,3 ; 1,2,3,0 x dih 27', 'perm 4 1,0,2,3 ; 1,2,3,0 x dih 29',
                 'perm 4 1,0,2,3 ; 1,2,3,0 x dih 31', 'perm 4 1,0,2,3 ; 1,2,3,0 x dih 33', 'perm 4 1,0,2,3 ; 1,2,3,0 x dih 35',
                 'agl1 37', 'agl1 41', 'agl1 29 x cyc 2', 'agl1 23 x cyc 3', 'agl1 19 x cyc 4', 'agl1 19 x cyc 5',
                 'agl1 7 x cyc 30', 'agl1 7 x cyc 32', 'agl1 7 x cyc 34', 'agl1 7 x cyc 36',
                 'sl2 3 x cyc 100', 'sl2 3 x cyc 110', 'sl2 3 x cyc 120', 'sl2 3 x cyc 130', 'sl2 3 x cyc 140',
                 'psl2 7 x dih 3', 'heis 5 x cyc 10', 'heis 5 x cyc 11', 'heis 5 x cyc 12', 'heis 5 x cyc 13',
                 'heis 3 x cyc 44', 'heis 3 x cyc 50', 'heis 3 x cyc 56', 'heis 3 x cyc 62',
                 'heis 7 x cyc 4', 'dih 12 x dih 25', 'dih 15 x dih 20', 'dih 20 x dih 15', 'dih 10 x dih 30',
                 'dih 17 x dih 9', 'dih 13 x dih 13', 'dih 11 x dih 16', 'dih 25 x dih 6']
        for s in specs:
            jobs.append((s.replace(' ', '_').replace(';', '').replace(',', ''), ('spec', s)))
    elif part == 'dicyc':
        for n in range(297, 426):
            jobs.append((f'dicyclic_n{n}', ('dicyclic', n)))
    elif part == 'gendih':
        for a, b in [(2, 300), (2, 2 * 150) , (3, 200), (5, 120), (6, 100), (10, 60), (2, 2 * 2 * 75 // 2 * 1)]:
            pass
        cands = []
        for a in range(2, 40):
            for b in range(a, 900):
                if a * b < 593 or a * b > 850 or b % a != 0:
                    continue
                cands.append((a, b))
        for a, b in cands:
            jobs.append((f'gendih_{a}x{b}', ('gendih', a, b)))
    for name, spec in jobs:
        if spec[0] == 'spec':
            run(name, ('spec', spec[1]))
        else:
            run(name, spec)
    log(f'DONE part {part} jobs {len(jobs)}')
