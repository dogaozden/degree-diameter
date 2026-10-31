# enumv.py BASE TAB K OUT: exhaustive over voltages of the last K base edges (Z_2 here), EVAL cost via vl; writes best base.
import sys, subprocess, os, itertools
base, tab, K, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
L = open(base).read().split('\n')
b, E = map(int, L[0].split()[:2]); side = L[1]
ed = [l.split() for l in L[2:2 + E]]
env = dict(os.environ, EVAL='1')
best = (10**9, None)
for pat in itertools.product(range(2), repeat=K):
    rows = ed[:E - K] + [[e[0], e[1], str(p)] for e, p in zip(ed[E - K:], pat)]
    tmp = 'samp/enum.base'
    with open(tmp, 'w') as f:
        f.write(f"{b} {E}\n{side}\n" + '\n'.join(' '.join(r) for r in rows) + '\n')
    o = subprocess.run(['../shared/vl', tmp, tab], env=env, capture_output=True, text=True).stdout
    c = int(o.strip().split('\n')[-1].split()[2])
    if c < best[0]:
        best = (c, rows); open(out, 'w').write(f"{b} {E}\n{side}\n" + '\n'.join(' '.join(r) for r in rows) + '\n')
print("best", best[0])
