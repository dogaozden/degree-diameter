# dmg.py BASE TAB OUT: vl cost of the base with one edge deleted, for every edge (damage). Writes "cost edge_index u w" lines.
import sys, subprocess, os
base, tab, out = sys.argv[1], sys.argv[2], sys.argv[3]
L = open(base).read().split('\n')
b, E = map(int, L[0].split()[:2]); side = L[1]
ed = [l for l in L[2:2 + E]]
env = dict(os.environ, EVAL='1')
res = []
for i in range(E):
    tmp = 'samp/dmg_tmp.base'
    with open(tmp, 'w') as f:
        f.write(f"{b} {E-1}\n{side}\n" + '\n'.join(ed[:i] + ed[i+1:]) + '\n')
    o = subprocess.run(['../shared/vl', tmp, tab], env=env, capture_output=True, text=True).stdout
    c = int(o.strip().split('\n')[-1].split()[2])
    res.append((c, i, ed[i]))
res.sort()
with open(out, 'w') as f:
    for c, i, e in res: f.write(f"{c} {i} {e}\n")
print("min", res[0], "median", res[len(res)//2][0], "max", res[-1][0])
