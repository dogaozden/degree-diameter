#!/usr/bin/env python3
"""finalize.py: among candidate orbit-id files (args), expand each to lines, keep the largest one that chkset accepts
and write it to c3/best_L.txt (falls back to the RL baseline, i.e. the orbits of start_o7.txt, if nothing is larger)."""
import subprocess, sys, shutil, numpy as np, os
C3 = '/home/user/degree-diameter/research/squads/c157b-r1/c3/'
CHK = '/home/user/degree-diameter/research/squads/c157b-r1/shared/chkset.py'
def check(fn):
    out = subprocess.run(['python3', CHK, 'L', fn], capture_output=True, text=True).stdout.strip()
    return out
best = None
for fn in sys.argv[1:]:
    if not os.path.exists(fn): continue
    ids = np.loadtxt(fn, dtype=np.int64).reshape(-1)
    if len(ids) == 0: continue
    tag = 'o7' if 'o7' in fn else 'o19'
    out = subprocess.run(['python3', C3 + 'convert.py', tag, fn, C3 + 'tmp_lines.txt'], capture_output=True, text=True)
    res = check(C3 + 'tmp_lines.txt')
    print(fn, res, flush=True)
    if res.startswith('VALID L'):
        size = int(res.split()[-1])
        if best is None or size > best[0]:
            best = (size, C3 + 'tmp_lines.txt', fn)
            shutil.copy(C3 + 'tmp_lines.txt', C3 + 'cand_%d_%s' % (size, os.path.basename(fn)))
print('BEST', best, flush=True)
