"""Turn a clique of admissible orbits (wclq2 output, GRAPH numbering) into a point set, verify it with the
independent scorer rules, then greedily add single points that are not collinear with anything chosen.
usage: union_fill.py PREFIX CLIQUE_FILE OUT_IDX [SEED]
PREFIX: the orbit_build.py output prefix (uses PREFIX_oid.npy and PREFIX_adm.npy)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r5/c2')
import ncl
from score_ncol import score
HEX = ncl.HEX
prefix, cf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
lines, coord, code = ncl.load_hex(); N = len(coord)
pl = ncl.point_lines_of(lines, N); nb = ncl.collinear_nbrs(lines, pl, N)
oid = np.load(prefix + '_oid.npy'); adm = np.load(prefix + '_adm.npy')
verts = [int(s.split()[0]) for s in open(cf) if s.strip() and not s.startswith('#')]
pts = np.nonzero(np.isin(oid, adm[verts]))[0].tolist()
ok, m, why = score(HEX, pts)
print('orbit union:', len(verts), 'orbits', m, 'points', 'valid' if ok else 'INVALID ' + why, flush=True)
assert ok
chosen = np.zeros(N, bool); chosen[pts] = True
blocked = np.zeros(N, bool); blocked[pts] = True
blocked[nb[np.array(pts)].reshape(-1)] = True
rng = np.random.default_rng(seed)
added = 0
for p in rng.permutation(N):
    if not blocked[p]:
        chosen[p] = True; blocked[p] = True; blocked[nb[p]] = True; added += 1
final = np.nonzero(chosen)[0].tolist()
ok2, m2, why2 = score(HEX, final)
print('greedy fill added', added, 'total', m2, 'valid' if ok2 else 'INVALID ' + why2, flush=True)
assert ok2
open(outf, 'w').write(f'# {m2} pairwise non-collinear points of H(9) (orbit union + greedy fill)\n' + '\n'.join(map(str, final)) + '\n')
print('wrote', outf)
