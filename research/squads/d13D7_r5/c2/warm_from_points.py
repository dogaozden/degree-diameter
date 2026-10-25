"""Map a valid point set onto the orbit graph of a group G (PREFIX_oid.npy, PREFIX_adm.npy): the orbits it meets
(each must be admissible, i.e. contained in the set) become a warm-start clique file in GRAPH numbering.
usage: warm_from_points.py PREFIX POINTFILE OUTFILE"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r5/c2')
import ncl
prefix, ptf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
oid = np.load(prefix + '_oid.npy'); adm = np.load(prefix + '_adm.npy')
pts = ncl.read_idx(ptf)
K0 = oid.max() + 1
pos = np.full(K0, -1, np.int64); pos[adm] = np.arange(len(adm))
orbs = np.unique(oid[np.array(pts)])
v = pos[orbs]
assert (v >= 0).all(), 'an orbit met by the set is not admissible'
open(outf, 'w').write(f'# warm start: {len(v)} orbits from {len(pts)} points\n' + '\n'.join(map(str, v.tolist())) + '\n')
print('orbits', len(v), 'points', len(pts), 'wrote', outf)
