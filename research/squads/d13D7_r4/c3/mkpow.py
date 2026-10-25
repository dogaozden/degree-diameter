#!/usr/bin/env python3
"""mkpow.py (card c3, squad round 4): write the generators of a power subgroup.
usage: mkpow.py Q GENSFILE J OUTFILE   ->  OUTFILE holds the generators (g^J for each generator g of GENSFILE)."""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbq as L  # noqa: E402

q, src, j, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4]
L.setq(q)
desc, gens = L.read_gens(src)
pw = [L.mpow(g, j) for g in gens]
with open(out, 'w') as f:
    f.write(f'# power {j} of ({desc}): order {L.order_of(pw[0])}\n')
    for i, g in enumerate(pw):
        f.write(f'# generator {i}\n')
        f.write(L.mat_to_text(g))
print('wrote', out, 'order', L.order_of(pw[0]))
