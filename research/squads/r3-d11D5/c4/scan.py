import random, subprocess, sys, os, json
sys.path.insert(0, '.')
from gen import *
kind = sys.argv[1]; N = int(sys.argv[2]); seed = int(sys.argv[3])
rng = random.Random(seed)
os.makedirs('starts', exist_ok=True)
res = []
for it in range(N):
    ln2, Ls, ps = build(kind, rng)
    sig2 = list(sig) + [n]          # sigma(x*) = l*
    fn = f'starts/{kind}_{seed}_{it}.in'
    write(fn, n + 1, dg, ln2, sig2)
    out = subprocess.run(['./po7', fn], env={**os.environ, 'SCORE': '1'}, capture_output=True, text=True).stdout
    c = int(out.split('cost=')[1].split()[0]) if 'cost=' in out else -1
    res.append((c, fn))
res.sort()
print(kind, 'costs', [c for c, _ in res[:15]], 'median', res[len(res)//2][0], 'max', res[-1][0])
json.dump(res[:20], open(f'top_{kind}_{seed}.json', 'w'))
