import sys, os, time, pickle, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise9/r1/a02')
from nonsplit_hi import table_ns, ok
B = '/home/user/degree-diameter/research/squads/raise9/bin'
budget = float(sys.argv[1]); t0 = time.time()
specs = pickle.load(open('nonsplit_dedup_hi.pkl', 'rb'))
done = set(l.split('\t')[0] for l in open('results_ns_hi.tsv')) if os.path.exists('results_ns_hi.tsv') else set()
os.makedirs('tmp', exist_ok=True); os.makedirs('hits', exist_ok=True)
n = 0
for (N, m, k, r, s) in specs:
    tag = f"nsh_m{m}_k{k}_r{r}_s{s}"
    if tag in done: continue
    if time.time() - t0 > budget: break
    T = table_ns(m, k, r, s)
    if not ok(T):
        with open('results_ns_hi.tsv', 'a') as f: f.write(f"{tag}\t{N}\tNOTGROUP\tNA\tNA\tnone\tbad\n")
        continue
    fn = f"tmp/ns_{n}.bin"
    with open(fn, 'wb') as f:
        np.array([N], dtype=np.int32).tofile(f); T.astype(np.uint16).tofile(f)
    out = subprocess.run([f"{B}/exh3", fn, '9', f"hits/{tag}"], capture_output=True, text=True, timeout=100).stdout
    os.remove(fn)
    gl = [l for l in out.splitlines() if l.startswith('GROUP')]
    mc = gl[0].split('mincost=')[1].split()[0] if gl else 'NA'
    c0 = gl[0].split('cost0_pairs=')[1].split()[0] if gl else 'NA'
    found = 'RESULT FOUND' in out
    with open('results_ns_hi.tsv', 'a') as f: f.write(f"{tag}\t{N}\t{mc}\t{c0}\tNA\t{'FOUND' if found else 'none'}\t{out.strip().splitlines()[-1] if out.strip() else 'EMPTY'}\n")
    n += 1
print(f"ran {n} in {time.time()-t0:.1f}s", flush=True)
