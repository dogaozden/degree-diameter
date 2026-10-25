# c1 feature builder: W(7) flags with canonical point / Pluecker-line coordinates (mod 7).
import numpy as np, subprocess, os, struct, re

ZDIR = '/home/user/degree-diameter/research/d11D5/z3'
OUT = '/home/user/degree-diameter/research/squads/r1-d11D5/c1'
P = 7
Q1 = 8
CHI = np.array([0, 0, 2, 1, 1, 2, 0], dtype=np.int64)   # cubic character of F_7^* as log_3 mod 3; chi(0):=0
INV = np.array([0, 1, 4, 5, 2, 3, 6], dtype=np.int64)


def load_gq(path=f'{ZDIR}/gq/gq_q7.bin'):
    with open(path, 'rb') as f:
        data = f.read()
    q, N, L = struct.unpack('<3i', data[:12])
    assert q == 7
    pl = np.frombuffer(data, dtype='<i4', count=L * Q1, offset=12).reshape(L, Q1).astype(np.int64)
    off = 12 + 4 * L * Q1
    co = np.frombuffer(data, dtype=np.uint8, count=N * 7, offset=off).reshape(N, 7)[:, :4].astype(np.int64) % P
    return N, L, pl, co


def normalize_rows(v):
    v = v % P
    idx = np.argmax(v != 0, axis=1)
    lead = v[np.arange(v.shape[0]), idx]
    return (v * INV[lead][:, None]) % P


N, L, pl, co = load_gq()
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
_x = co[pl[:, 0]]
_y = co[pl[:, 1]]
LPL = normalize_rows(np.stack([(_x[:, i] * _y[:, j] - _x[:, j] * _y[:, i]) % P for i, j in PAIRS], axis=1))
assert np.all((LPL[:, 0] + LPL[:, 5]) % P == 0), "lines must be totally isotropic"
FP = co[pl.reshape(-1)]                     # 3200 x 4 : point of flag f = l*8+k
FL = np.repeat(LPL, Q1, axis=0)             # 3200 x 6 : line of flag f
assert FP.shape == (3200, 4) and FL.shape == (3200, 6)
# incidence sanity: p lies on line l  <=>  p ^ l = 0 in Lambda^3 (4 triple equations)
# column order of LPL: 01,02,03,12,13,23 ; (p^l)_{ijk} = p_i l_jk - p_j l_ik + p_k l_ij
_p = FP
_l = FL
_c = {(0,1):0,(0,2):1,(0,3):2,(1,2):3,(1,3):4,(2,3):5}
def _lc(i,j): return _l[:, _c[(i,j)]]
trip = [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]
for (i,j,k) in trip:
    val = (_p[:, i]*_lc(j,k) - _p[:, j]*_lc(i,k) + _p[:, k]*_lc(i,j)) % P
    assert np.all(val == 0), "flag incidence check failed"


def zcov_cost(labels, tag='tmp'):
    """labels: length-3200 ints (any integers, reduced mod 3 by zcov). Returns zcov cost."""
    fn = os.path.join(OUT, f'labels_{tag}.txt')
    np.savetxt(fn, np.asarray(labels) % 3, fmt='%d')
    r = subprocess.run(['./zcov', '7', '3'], cwd=ZDIR,
                       env={**os.environ, 'SCORE': '1', 'IN': fn},
                       capture_output=True, text=True, timeout=300)
    m = re.search(r'cost=(\d+)', r.stdout)
    if not m:
        raise RuntimeError(r.stdout + r.stderr)
    return int(m.group(1))
