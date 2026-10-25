#!/usr/bin/env python3
"""score_relaxed2.py: exact scorer for the relaxed (15,7) construction with ANY level-type pattern T (7 letters H/D).
It finds the bottleneck friendly transitions (the only friendly outgoing transition of a level, the only friendly
incoming one of a level), takes their freed sets from the command line, and for every bottleneck transition t = j -> j2
uses every NON-bottleneck friendly transition into j and out of j2 as cover providers; every provider set is designed
with a private covering element for each paired element of the bottleneck sets it serves (design_cover.py + design3.py),
the other non-bottleneck friendly sets are master's sets or collineation images. Then hub assignment with drops
(v3_drop.py / tm3_build.py) and n = 14*177,156 + KB + KA.
usage: score_relaxed2.py HEXBIN MIRROR_SOL BASEDIR T WORKDIR j:k:FILE ...   (one j:k:FILE per bottleneck transition;
       BASEDIR holds RH.txt RHb.txt RL.txt RLb.txt)"""
import sys, os, shutil, subprocess
import numpy as np
D = os.path.dirname(os.path.abspath(__file__))
hexfn, mirfn, based, T, wd = sys.argv[1:6]
hexfn = os.path.abspath(hexfn); mirfn = os.path.abspath(mirfn)
L = 7; TY = [1 if c == 'D' else 0 for c in T]
fr = [(j, k) for j in range(L) for k in (1, 2, 3) if TY[j] != TY[(j + k) % L]]
out = {j: [t for t in fr if t[0] == j] for j in range(L)}
inn = {j: [t for t in fr if (t[0] + t[1]) % L == j] for j in range(L)}
bott = set(out[j][0] for j in range(L) if len(out[j]) == 1) | set(inn[j][0] for j in range(L) if len(inn[j]) == 1)
given = {}
for a in sys.argv[6:]:
    j, k, f = a.split(':', 2); given[(int(j), int(k))] = os.path.abspath(f)
assert set(given) == bott, ('bottleneck transitions are', sorted(bott))
os.makedirs(wd, exist_ok=True)
for f in ('RH.txt', 'RHb.txt', 'RL.txt', 'RLb.txt'): shutil.copy(os.path.join(based, f), os.path.join(wd, f))
shutil.copy(mirfn, os.path.join(wd, os.path.basename(mirfn)))
def run(*a):
    r = subprocess.run([sys.executable] + list(a), capture_output=True, text=True, cwd=wd)
    if r.returncode != 0: sys.exit(f'failed: {a}\n{r.stdout}\n{r.stderr}')
    return r.stdout
need = {}
for t in sorted(bott):
    j, k = t; j2 = (j + k) % L; kind = 'P' if TY[j] == 0 else 'L'
    fn = f'B{j}{j2}.txt'; shutil.copy(given[t], os.path.join(wd, fn))
    run(os.path.join(D, 'paired.py'), hexfn, kind, fn, f'B{j}{j2}.paired')
    p1 = [s for s in inn[j] if s not in bott]; p2 = [s for s in out[j2] if s not in bott]
    assert p1 and p2, f'no non-bottleneck cover provider for {t}'
    # role B: the provider's B-slots at level j (it ends at j) serve the C1 demands; role A: its A-slots at level j2
    for s in p1: need.setdefault(s, {'A': [], 'B': []})['B'].append(f'B{j}{j2}.paired')
    for s in p2: need.setdefault(s, {'A': [], 'B': []})['A'].append(f'B{j}{j2}.paired')
spec = [f'T {T}']
alt = {0: ['RH.txt', 'RHb.txt'], 1: ['RL.txt', 'RLb.txt']}; cnt = {0: 0, 1: 0}
for (j, k) in fr:
    j2 = (j + k) % L
    if (j, k) in bott: spec.append(f'{j} {k} B{j}{j2}.txt'); continue
    a = TY[j]; base = alt[a][cnt[a] % 2]; cnt[a] += 1
    if (j, k) in need:
        nfs = {}
        for role in ('A', 'B'):
            if need[(j, k)][role]:
                ids = np.unique(np.concatenate([np.loadtxt(os.path.join(wd, f), dtype=np.int64).reshape(-1) for f in need[(j, k)][role]]))
                nfs[role] = f'need{role}_{j}{j2}.txt'; np.savetxt(os.path.join(wd, nfs[role]), ids, fmt='%d')
            else: nfs[role] = '-'
        allf = f'need_{j}{j2}.txt'
        np.savetxt(os.path.join(wd, allf), np.unique(np.concatenate([np.loadtxt(os.path.join(wd, nfs[r]), dtype=np.int64).reshape(-1) for r in 'AB' if nfs[r] != '-'])), fmt='%d')
        m = 'L' if a == 1 else 'P'        # provider frees lines (covers points) or points (covers lines)
        print(run(os.path.join(D, 'design_cover.py'), hexfn, m, allf, base, str(10 * j + k), f'C{j}{j2}.txt'), end='')
        print(run(os.path.join(D, 'design4.py'), hexfn, m, nfs['A'], nfs['B'], f'C{j}{j2}.txt', '7', '2000', f'C{j}{j2}.txt'), end='')
        spec.append(f'{j} {k} C{j}{j2}.txt')
    else:
        spec.append(f'{j} {k} {base}')
open(os.path.join(wd, 'spec.txt'), 'w').write('\n'.join(spec) + '\n')
o = run(os.path.join(D, 'v3_drop.py'), hexfn, os.path.basename(mirfn), 'spec.txt', '1', 'assign.sol')
last = [l for l in o.split('\n') if l.startswith('free A-slots')][-1]
KB, KA = (int(v) for v in last.split('-> hubs')[1].split())
drops = sum(int(l.split()[1]) for l in o.split('\n') if l.strip().startswith('dropped'))
print(last)
print(f'bottleneck {sorted(bott)}; dropped {drops} elements')
print(f'SCORE n = {14 * 177156 + KB + KA} (hubs {KB} + {KA}); hub graph still to be added (v3_hub.sh)')
