import sys, subprocess, os, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import groups
EXH = '/home/user/degree-diameter/research/squads/beyond11b/bin/exh3'
# usage: run1.py SPEC TAG D   -> builds table, runs exh3, prints result
spec, tag, D = sys.argv[1], sys.argv[2], sys.argv[3]
T = groups.table(spec)
N = T.shape[0]
fn = f"/home/user/degree-diameter/research/squads/beyond11b/r2/h11/t_{tag}.bin"
with open(fn, 'wb') as f:
    f.write(np.array([N], dtype=np.int32).tobytes()); f.write(T.astype(np.uint16).tobytes())
del T
t0 = time.time()
r = subprocess.run([EXH, fn, D, f"/home/user/degree-diameter/research/squads/beyond11b/r2/h11/hit_{tag}"], capture_output=True, text=True, timeout=600)
print(f"{spec} | N={N} | {time.time()-t0:.1f}s | " + " | ".join(l for l in r.stdout.splitlines() if l.startswith(('GROUP','RESULT')))[:400] + (r.stderr[-200:] if r.returncode else ''), flush=True)
os.remove(fn)
