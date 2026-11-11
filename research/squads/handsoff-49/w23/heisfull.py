#!/usr/bin/env python3
"""All diagonal automorphisms of Heis(5) x Z_5: x->al x, y->be y, z->al*be z (Heis part), w->lam w, al,be,lam in Z_5^*.
Writes tabs/hd_{al}{be}{lam}.bin and manifest fam_manifest_heisfull.tsv (dedup by invariants)."""
import sys, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from mkg15 import *
from fam15 import write_one, fpf_ok
import fam15
H = '/home/user/degree-diameter/research/squads/handsoff-49/w15'
TPh = GR.table('heis 5 x cyc 5')
coords = coords_heis(5, 5)
Pn = len(coords)
idx = index_of(coords)
out = open(f'{H}/fam_manifest_heisfull.tsv', 'a')
seen = {}
for al in (1, 2, 3, 4):
    for be in (1, 2, 3, 4):
        for lam in (1, 2, 3, 4):
            perm = np.empty(Pn, dtype=np.int64)
            for i, (x, y, z, w) in enumerate(coords):
                perm[i] = idx[((al * x) % 5, (be * y) % 5, (al * be * z) % 5, (lam * w) % 5)]
            check_automorphism(TPh, perm)
            T = semidirect(TPh, perm)
            inv = invariants(T)
            key = (tuple(sorted(inv['hist'].items())), inv['centre'], inv['ab'])
            if key in seen:
                seen[key].append((al, be, lam)); continue
            seen[key] = [(al, be, lam)]
            write_one(f'hd_{al}{be}{lam}', T, f'Heis(5)xZ5 diag al={al} be={be} lam={lam}', out)
print('classes', len(seen))
for k, v in seen.items():
    print(v[0], 'equiv', v[1:], 'centre', k[1], 'ab', k[2])
