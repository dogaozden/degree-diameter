"""Expand a set of admissible-orbit indices (quotient vertices) into points of H(7).
usage: expand.py PREFIX ORBIDX_FILE OUT_POINTS"""
import sys
import numpy as np
prefix, idxf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
orb_adm = np.fromfile(prefix + '_orb.bin', dtype=np.int32)      # admissible index -> orbit id
orbof = np.fromfile(prefix + '_orbof.bin', dtype=np.int32)      # point -> orbit id
sel = [int(x) for x in open(idxf).read().split()]
orbs = set(int(orb_adm[i]) for i in sel)
pts = np.nonzero(np.isin(orbof, list(orbs)))[0]
open(outf, 'w').write('\n'.join(map(str, pts.tolist())) + '\n')
print('orbits', len(orbs), 'points', len(pts))
