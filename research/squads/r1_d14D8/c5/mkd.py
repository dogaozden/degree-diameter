"""c5 generator: base graph = H(13) minus a perfect matching F plus a perfect matching M (point-line, M avoids all
hexagon incidences, so M(p) is at hexagon distance 3 or 5). Degree 14 = 13 hexagon edges + 1 matching edge per vertex.
Voltages: hexagon edges from hexvolt (N x 14 array indexed [line, position], default 0); M-edges from psi (N,) in Z_m.
Usage: python3 mkd.py OUT.txt m seedF seedM hexmode psimode [args]
  hexmode: zero | rand (uniform in Z_m) | file:<npy path>
  psimode: rand (uniform in Z_m) | file:<npy path>  (psi values are taken mod m)
  F and M are reproducible from seedF / seedM; F is saved as work/F_<seedF>.npy, M as work/M_<seedM>_<tag>.npy."""
import sys, os, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, dist_from_point
HERE = '/home/user/degree-diameter/research/squads/r1_d14D8/c5'
WORK = HERE + '/work'
Q = 13

def get_N_LP_PL_coord():
    return load(Q)

def get_F(N, PL, seed):
    fn = f'{WORK}/F_{seed}.npy'
    if os.path.exists(fn):
        return np.load(fn)
    adj_fn = f'{WORK}/adjPL.bin'
    if not os.path.exists(adj_fn):
        with open(adj_fn, 'wb') as f:
            np.array([N, PL.shape[1]], dtype=np.int32).tofile(f)
            PL.astype(np.int32).tofile(f)
    out = f'{WORK}/F_raw_{seed}.bin'
    r = subprocess.run([HERE + '/hk', adj_fn, out, str(seed)], capture_output=True, text=True)
    sys.stderr.write(r.stderr)
    assert r.returncode == 0, 'matching failed'
    F = np.fromfile(out, dtype=np.int32).astype(np.int64)
    np.save(fn, F)
    os.remove(out)
    return F

def make_M(N, PL, rng):
    """random perfect matching points -> lines with M(p) not incident to p"""
    M = rng.permutation(N).astype(np.int64)
    def bad(p):
        return (PL[p] == M[p]).any()
    conflicts = [p for p in range(N) if bad(p)]
    while conflicts:
        nxt = []
        for p in conflicts:
            if not bad(p):
                continue
            for _ in range(100):
                q = int(rng.integers(N))
                M[p], M[q] = M[q], M[p]
                if not bad(p) and not bad(q):
                    break
                M[p], M[q] = M[q], M[p]
            else:
                nxt.append(p)
            if bad(p):
                nxt.append(p)
        conflicts = sorted(set(nxt))
    return M

def write_base_fast(fn, N, m, E):
    with open(fn, 'w') as f:
        f.write(f'{N} {N} {m}\n')
        chunk = 1000000
        for s in range(0, len(E), chunk):
            blk = E[s:s + chunk]
            f.write('\n'.join(f'{a} {b} {c}' for a, b, c in blk.tolist()))
            f.write('\n')

def build(out, m, seedF, seedM, hexmode, psimode, tag='0'):
    N, LP, PL, coord = get_N_LP_PL_coord()
    F = get_F(N, PL, seedF)
    rng = np.random.default_rng(seedM)
    mfn = f'{WORK}/M_{seedM}_{tag}.npy'
    if os.path.exists(mfn):
        M = np.load(mfn)
    else:
        M = make_M(N, PL, rng)
        np.save(mfn, M)
    rng2 = np.random.default_rng(seedM + 1000003)
    if hexmode == 'zero':
        hexvolt = np.zeros((N, LP.shape[1]), dtype=np.int64)
    elif hexmode == 'rand':
        hexvolt = rng2.integers(0, m, (N, LP.shape[1]))
    else:
        hexvolt = np.load(hexmode.split(':', 1)[1])
    if psimode == 'rand':
        psi = rng2.integers(0, m, N)
    else:
        psi = np.load(psimode.split(':', 1)[1])
    ls = np.repeat(np.arange(N), LP.shape[1])
    ps = LP.reshape(-1).astype(np.int64)
    mask = F[ps] != ls                      # keep hexagon edges except the matching F
    hexE = np.stack([ps[mask], ls[mask], hexvolt.reshape(-1)[mask] % m], axis=1)
    mE = np.stack([np.arange(N), M, psi % m], axis=1)
    E = np.concatenate([hexE, mE]).astype(np.int64)
    write_base_fast(out, N, m, E)
    return out

if __name__ == '__main__':
    out, m, seedF, seedM = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    hexmode, psimode = sys.argv[5], sys.argv[6]
    tag = sys.argv[7] if len(sys.argv) > 7 else '0'
    build(out, m, seedF, seedM, hexmode, psimode, tag)
    print('wrote', out)
