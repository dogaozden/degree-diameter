import sys, os, subprocess, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import groups
B = '/home/user/degree-diameter/research/squads/raise9/bin'
D = 9
budget = float(sys.argv[1]) if len(sys.argv) > 1 else 90
t0 = time.time()
done = set()
if os.path.exists('results.tsv'):
    for l in open('results.tsv'):
        done.add(l.split('\t')[0])
os.makedirs('tmp', exist_ok=True)
queue = [l.strip() for l in open('queue.txt') if l.strip()]
todo = [q for q in queue if q not in done]
n_run = 0
for spec in todo:
    if time.time() - t0 > budget: break
    T = groups.table(spec)
    N = len(T)
    fn = f"tmp/t_{N}_{n_run}.bin"
    with open(fn, 'wb') as f:
        np.array([N], dtype=np.int32).tofile(f); T.astype(np.uint16).tofile(f)
    tag = spec.replace(' ', '_')
    try:
        out = subprocess.run([f"{B}/exh3", fn, str(D), f"hits/{tag}"], capture_output=True, text=True, timeout=100).stdout
    except Exception as e:
        out = 'ERR ' + str(e)
    os.remove(fn)
    gl = [l for l in out.splitlines() if l.startswith('GROUP')]
    found = 'RESULT FOUND' in out
    mc, c0, pairs = 'NA', 'NA', 'NA'
    if gl:
        g = gl[0]
        mc = g.split('mincost=')[1].split()[0]
        c0 = g.split('cost0_pairs=')[1].split()[0]
        pairs = g.split('pairs=')[1].split()[0]
    with open('results.tsv', 'a') as f:
        f.write(f"{spec}\t{N}\t{mc}\t{c0}\t{pairs}\t{'FOUND' if found else 'none'}\t{out.strip().splitlines()[-1] if out.strip() else 'EMPTY'}\n")
    n_run += 1
print(f"ran {n_run} groups in {time.time()-t0:.1f}s; remaining {len(todo)-n_run}", flush=True)
