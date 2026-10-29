"""Run sat_hatmodel.py on every conic-adapted five-hat frame (Z plus two conjugate pairs) and six-hat frame
(Z, Z' plus two pairs), q = 5, 7, 9, 11, 13, with and without imposed self-polarity; four-hat controls."""
import itertools
import subprocess
import sys

import coords

PY = sys.executable
for q in (5, 7, 9, 11, 13):
    F = coords.GF(q)
    pairs = sorted({min(u, F.neg(u)) for u in range(1, q)})
    runs = [(['Z', "Z'", str(pairs[0])], 'control four hats')]
    for u, v in itertools.combinations(pairs, 2):
        runs.append((['Z', str(u), str(v)], 'five hats'))
    for u, v in itertools.combinations(pairs, 2):
        runs.append((['Z', "Z'", str(u), str(v)], 'six hats'))
    for marks, what in runs:
        for polar in (False, True):
            cmd = [PY, 'sat_hatmodel.py', str(q), '1', '1'] + marks + (['--polar'] if polar else [])
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=900).stdout.strip()
            print(f'{what:18s} {out}', flush=True)
