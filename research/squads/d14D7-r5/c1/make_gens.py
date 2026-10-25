#!/usr/bin/env python3
"""Write one orbclq generator file per subgroup class of PGL(2,11) (principal action on sextics)."""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sext
from collections import Counter

GDIR = os.path.join(HERE, 'gens')
os.makedirs(GDIR, exist_ok=True)
cl = sext.enumerate_classes()
rows = []
for cls in sorted(cl, key=lambda c: (c[0], c[1])):
    order, sig = cls
    gens = cl[cls]
    name = f"o{order}_" + "".join(f"{k}x{v}" for k, v in sig if k > 1)
    name = name.replace(',', '').replace('(', '').replace(')', '')
    path = os.path.join(GDIR, name + '.txt')
    sext.write_std(path, gens, f"PGL(2,11) subgroup: order {order}, element orders {sig}; 2x2 generators {gens}")
    rows.append({'name': name, 'order': order, 'sig': sig, 'gens': [list(map(list, g)) for g in gens], 'file': path})
    print(name, order, len(gens))
json.dump(rows, open(os.path.join(HERE, 'classes.json'), 'w'), indent=1)
