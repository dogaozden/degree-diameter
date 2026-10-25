"""Orbits of a group G = <alpha^a, phi^b> on the points of H(9); admissible orbits (no two collinear points inside);
orbit compatibility graph (no collinear pair across).  Writes GRAPH binary for wclq2 and a pickle of the orbit lists.
usage: orbit_build.py SPEC OUTPREFIX     SPEC like 'a1' (<alpha>), 'a2', 'a3', 'a6', 'ap' (<alpha,phi>), 'a2p', 'a3p', 'p'
Graph binary: int32 K, int32 W, int32 w[K], uint64 rows[K*W] (bit j of row i set iff orbit i and j are compatible)."""
import sys, time, pickle, math
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r5/c2')
import ncl

def power(perm, k):
    r = np.arange(len(perm))
    for _ in range(k): r = perm[r]
    return r

def group_gens(spec, alpha, phi):
    spec = spec.lower()
    gens = []
    if spec.startswith('a'):
        k = int(spec[1]) if spec[1].isdigit() else 1
        gens.append(power(alpha, k))
        spec = spec[2:] if spec[1].isdigit() else spec[1:]
    if 'p' in spec:
        gens.append(phi)
    return gens

def build(spec, lines, coord, code, pl, nb, alpha, phi, N):
    gens = group_gens(spec, alpha, phi)
    oid, K0 = ncl.orbits_of(gens, N)
    sizes = np.bincount(oid, minlength=K0)
    # internal collinearity: a point of orbit o with a collinear neighbour in o
    bad = np.zeros(K0, bool)
    same = oid[nb] == oid[:, None]          # N x 90
    bad[np.unique(oid[np.nonzero(same.any(axis=1))[0]])] = True
    adm = np.nonzero(~bad)[0]
    newid = -np.ones(K0, np.int64); newid[adm] = np.arange(len(adm))
    K = len(adm)
    # conflicts between admissible orbits
    pa = oid[np.repeat(np.arange(N), 90)]; pb = oid[nb.reshape(-1)]
    m = (newid[pa] >= 0) & (newid[pb] >= 0) & (pa != pb)
    ca = newid[pa[m]]; cb = newid[pb[m]]
    W = (K + 63) // 64
    adjbits = np.zeros((K, W), np.uint64)
    # full compatibility = all pairs minus conflicts
    full = np.ones((K, K), bool); np.fill_diagonal(full, False)
    full[ca, cb] = False
    w = sizes[adm].astype(np.int32)
    return dict(gens=gens, oid=oid, adm=adm, newid=newid, K=K, W=W, w=w, full=full, sizes=sizes)

def write_graph(path, K, W, w, full):
    rows = np.zeros((K, W), np.uint64)
    pad = np.zeros((K, W * 64), bool); pad[:, :K] = full
    bits = np.packbits(pad.reshape(K, W, 64)[:, :, ::-1], axis=2, bitorder='big')  # placeholder, replaced below
    # explicit little bit-order packing: bit j of word j//64 -> value 1 << (j % 64)
    out = np.zeros((K, W), np.uint64)
    for j in range(64):
        cols = np.arange(j, W * 64, 64)
        cols = cols[cols < K]
        if len(cols) == 0: continue
        out[:, cols // 64] |= (full[:, cols].astype(np.uint64) << np.uint64(j))
    with open(path, 'wb') as f:
        np.array([K, W], np.int32).tofile(f)
        np.asarray(w, np.int32).tofile(f)
        out.tofile(f)

if __name__ == '__main__':
    spec, outp = sys.argv[1], sys.argv[2]
    t0 = time.time()
    lines, coord, code = ncl.load_hex(); N = len(coord)
    pl = ncl.point_lines_of(lines, N)
    nb = ncl.collinear_nbrs(lines, pl, N)
    alpha = ncl.alpha_perm(N); phi = ncl.frob_perm(coord, code)
    D = build(spec, lines, coord, code, pl, nb, alpha, phi, N)
    print(f'spec {spec}: orbits {len(D["sizes"])}, admissible {D["K"]}, sizes of admissible:',
          sorted(np.unique(D['w']).tolist()), 'orbit count by size:',
          {int(s): int(c) for s, c in zip(*np.unique(D['w'], return_counts=True))}, flush=True)
    print('compatible pairs:', int(D['full'].sum() // 2), 'density', round(float(D['full'].mean()), 4), flush=True)
    write_graph(outp + '.graph', D['K'], D['W'], D['w'], D['full'])
    np.save(outp + '_oid.npy', D['oid']); np.save(outp + '_adm.npy', D['adm'])
    print('wrote', outp + '.graph', 'time', round(time.time() - t0, 1), 's', flush=True)
