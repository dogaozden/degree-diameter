#!/usr/bin/env python3
"""Full enumeration of alpha-closed integer families (reps from the [-2,2] box) screened on q = 29,41,53 with haar_ecc (PSL)."""
import json, itertools, math, subprocess, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
HAAR = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
GEN = os.path.join(HERE, 'gen_int.py')
reps = [tuple(x) for x in json.load(open(os.path.join(HERE, 'orbit_reps.json')))]
def tok(X): return ':'.join(str(t) for t in X)
def gen(q, toks):
    return subprocess.run(['python3', GEN, str(q), '1'] + toks, capture_output=True, text=True).stdout
def ecc(q, toks, Delta):
    g = gen(q, toks)
    if not g.strip(): return None
    r = subprocess.run([HAAR, 'psl', str(q), '1'], input=g, capture_output=True, text=True, timeout=900)
    import re
    m = re.search(r'Delta=(\d+) .*compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
    if not m or m.group(5) != 'yes' or m.group(2) != m.group(3): return None
    d, n, diam = int(m.group(1)), int(m.group(2)), int(m.group(6))
    assert d == Delta, (d, Delta)
    return diam - math.log(n // 2) / math.log(Delta - 1)
SCREEN = [29, 41, 53]
out = []
for Delta, nf, no in [(8, 2, 2), (10, 1, 3)]:
    for fixed in itertools.combinations(['I', 'W', 'V'], nf):
        for orbs in itertools.combinations(range(len(reps)), no):
            toks = list(fixed) + [tok(reps[i]) for i in orbs]
            ex = [ecc(q, toks, Delta) for q in SCREEN]
            ok = all(e is not None for e in ex)
            mean = sum(ex) / len(ex) if ok else None
            out.append({'Delta': Delta, 'toks': toks, 'screen_mean': mean if mean is None else round(mean, 4),
                        'screen_ex': [None if e is None else round(e, 3) for e in ex]})
json.dump(out, open(os.path.join(HERE, 'screen_all.json'), 'w'), indent=0)
for Delta in (8, 10):
    rows = sorted([r for r in out if r['Delta'] == Delta and r['screen_mean'] is not None], key=lambda r: r['screen_mean'])
    print(f'Delta={Delta}: {len(rows)} valid of {sum(1 for r in out if r["Delta"]==Delta)}')
    for r in rows[:8]: print(r['screen_mean'], r['screen_ex'], ' '.join(r['toks']))
