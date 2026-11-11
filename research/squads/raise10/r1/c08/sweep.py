import sys, subprocess, os, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/tools')
import groups
D = 10
C = '/home/user/degree-diameter/research/squads/raise10/r1/c08'
budget = float(sys.argv[1])
lst = [tuple(map(int, l.split())) for l in open(C + '/meta_list2.txt') if l.strip()]
done = set()
if os.path.exists(C + '/done.txt'):
    done = set(open(C + '/done.txt').read().split('\n'))
t0 = time.time()
n = 0
for (N, m, k, r) in lst:
    if time.time() - t0 > budget: break
    key = f'{m} {k} {r}'
    if key in done: continue
    T = groups.table(f"meta {m} {k} {r}")
    fn = f"{C}/t_{m}_{k}_{r}.bin"
    with open(fn, 'wb') as f:
        f.write(np.array([N], dtype=np.int32).tobytes()); f.write(T.astype(np.uint16).tobytes())
    p = subprocess.run(["timeout", "100", "nice", "-n", "10", "/home/user/degree-diameter/research/squads/raise10/tools/bin/exh3", fn, str(D), f"{C}/hit_meta_{m}_{k}_{r}"], capture_output=True, text=True, env=dict(os.environ, THREADS="1", OMP_NUM_THREADS="1"))
    os.remove(fn)
    lines = [l for l in p.stdout.splitlines() if l.strip()]
    with open(C + '/sweep_log.txt', 'a') as lf:
        lf.write(f"meta {m} {k} {r} N={N} rc={p.returncode} | " + (" || ".join(lines[-3:]) if lines else p.stderr[-200:]) + "\n")
    with open(C + '/done.txt', 'a') as df: df.write(key + '\n')
    n += 1
print("done", n, "this chunk; elapsed", round(time.time() - t0, 1))
