# h03: abc groups (split abelian-by-cyclic, components p:d with d >= 2) of orders 217..230 not yet in index.txt
import sys, os, subprocess, itertools, math
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r4/h03')
import importlib.util
spec = importlib.util.spec_from_file_location('mk', '/home/user/degree-diameter/research/squads/b48/r4/h03/mkgroups.py')
src = open('/home/user/degree-diameter/research/squads/b48/r4/h03/mkgroups.py').read().split('cands = []')[0]
ns = {}; exec(src, ns)
signature, assoc_ok = ns['signature'], ns['assoc_ok']
ABC = '/home/user/degree-diameter/research/squads/b48/tools/abc.py'
OUT = '/home/user/degree-diameter/research/squads/b48/r4/h03/groups'
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
def ordmod(p, d):
    x, o = p % d, 1
    while x != 1: x = x * p % d; o += 1
    return o
def isprime(n): return n > 1 and all(n % q for q in range(2, int(n**0.5) + 1))
# component (p, d): f = ord_d(p), size p^f, needs d | k, p not dividing d
comps = []
for p in PRIMES:
    for d in range(2, 231):
        if d % p == 0: continue
        f = ordmod(p, d) if d > 1 else 1
        if p ** f > 230: continue
        comps.append((p, d, p ** f))
existing = set()
for line in open('/home/user/degree-diameter/research/squads/b48/r4/h03/index.txt'):
    fn = line.split()[-1]
    N = int(np.fromfile(fn, dtype=np.int32, count=1)[0])
    tab = np.fromfile(fn, dtype=np.uint16, offset=4).reshape(N, N).astype(np.int64)
    existing.add(signature(tab)[0])
made = []
for L in (1, 2, 3):
    for combo in itertools.combinations(comps, L):
        if len({c[0] for c in combo}) < L and L > 1 and False: pass
        ps = [c[0] for c in combo]
        size = 1
        for c in combo: size *= c[2]
        if size > 230: continue
        for k in range(2, 231):
            if 217 > k * size or k * size > 230: continue
            if any(k % c[1] for c in combo): continue
            if k * size < 217: continue
            N = k * size
            if any(c[1] == 2 for c in combo) and L == 1 and False: pass
            spec = f"{k} " + ",".join(f"{p}:{d}" for p, d, _ in combo)
            tb = f"{OUT}/tmp_abc.bin"
            r = subprocess.run([sys.executable, ABC, 'build', spec, tb], capture_output=True, text=True)
            if r.returncode != 0: continue
            n = int(np.fromfile(tb, dtype=np.int32, count=1)[0])
            tab = np.fromfile(tb, dtype=np.uint16, offset=4).reshape(n, n).astype(np.int64)
            if (tab == tab.T).all(): continue
            if not assoc_ok(tab): continue
            sg = signature(tab)[0]
            if sg in existing: continue
            existing.add(sg)
            fn = f"{OUT}/abc_{n}_{len(made):03d}.bin"
            os.replace(tb, fn)
            made.append(f"{n} abc {spec.replace(' ', '|')} {fn}")
            print(made[-1], file=sys.stderr)
os.path.exists(f"{OUT}/tmp_abc.bin") and os.remove(f"{OUT}/tmp_abc.bin")
with open('/home/user/degree-diameter/research/squads/b48/r4/h03/index.txt', 'a') as f:
    for line in made: f.write(line + "\n")
print(len(made), "abc groups added", file=sys.stderr)
