import sys, os, subprocess, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import groups
import itertools
def q8_table():
    # elements: (sign, unit) with unit in 0=1,1=i,2=j,3=k ; quaternion product
    basis = [(1,0),(1,1),(1,2),(1,3)]
    els = [(s,u) for s in (1,-1) for u in range(4)]
    def qm(a, b):
        s1,u1 = a; s2,u2 = b
        tab = {(0,0):(1,0),(0,1):(1,1),(0,2):(1,2),(0,3):(1,3),
               (1,0):(1,1),(1,1):(-1,0),(1,2):(1,3),(1,3):(-1,2),
               (2,0):(1,2),(2,1):(-1,3),(2,2):(-1,0),(2,3):(1,1),
               (3,0):(1,3),(3,1):(1,2),(3,2):(-1,1),(3,3):(-1,0)}
        s3,u3 = tab[(u1,u2)]
        return (s1*s2*s3, u3)
    # identity (1,0) must be index 0
    idx = {e:i for i,e in enumerate(els)}
    order = [(1,0)] + [e for e in els if e != (1,0)]
    idx = {e:i for i,e in enumerate(order)}
    N = 8
    T = np.empty((N,N), dtype=np.uint16)
    for i,g in enumerate(order):
        T[i] = [idx[qm(g,h)] for h in order]
    return T
def tab(spec):
    if ' x ' in spec:
        parts = spec.split(' x ')
        T = tab(parts[0])
        for p in parts[1:]:
            T = groups.t_prod(T, tab(p))
        return T
    if spec.strip() == 'q8':
        return q8_table()
    return groups.table(spec)
B = '/home/user/degree-diameter/research/squads/raise9/bin'
D = 9
budget = float(sys.argv[1]) if len(sys.argv) > 1 else 90
t0 = time.time()
QF = os.environ.get('QF','queue.txt'); RF = os.environ.get('RF','results.tsv')
done = set()
if os.path.exists(RF):
    for l in open(RF):
        done.add(l.split('\t')[0])
os.makedirs('tmp', exist_ok=True)
queue = [l.strip() for l in open(QF) if l.strip()]
todo = [q for q in queue if q not in done]
n_run = 0
for spec in todo:
    if time.time() - t0 > budget: break
    T = tab(spec)
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
    with open(RF, 'a') as f:
        f.write(f"{spec}\t{N}\t{mc}\t{c0}\t{pairs}\t{'FOUND' if found else 'none'}\t{out.strip().splitlines()[-1] if out.strip() else 'EMPTY'}\n")
    n_run += 1
print(f"ran {n_run} groups in {time.time()-t0:.1f}s; remaining {len(todo)-n_run}", flush=True)
