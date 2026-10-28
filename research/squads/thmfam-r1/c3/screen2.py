#!/usr/bin/env python3
"""Two-stage screen of all alpha-closed integer families (orbit reps from the [-2,2] box), PSL.
Stage 1: q=29 for all candidates. Stage 2: top 40 per Delta on q=41,53 (mean over 29,41,53)."""
import json, itertools, math, subprocess, re, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
HAAR = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
def mul(X, Y):
    a,b,c,d = X; e,g,h,i = Y; return (a*e+b*h, a*g+b*i, c*e+d*h, c*g+d*i)
w = (0,-1,1,-1); wi = (-1,1,-1,0); I = (1,0,0,1); V = mul(w,w)
def conj(X): return mul(mul(w,X),wi)
def lines(q, toks):
    S = []; seen = set()
    def key(X):
        X = tuple(t % q for t in X); lead = next(t for t in X if t)
        return tuple((-t) % q for t in X) if lead > (q-1)//2 else X
    def add(X):
        k = key(X)
        if k in seen: raise ValueError('dup')
        seen.add(k); S.append(tuple(t % q for t in X))
    for t in toks:
        if t == 'I': add(I)
        elif t == 'W': add(w)
        elif t == 'V': add(V)
        else:
            X = tuple(int(x) for x in t.split(':'))
            for Y in [X, conj(X), conj(conj(X))]: add(Y)
    return ''.join(f'{a} {b} {c} {d} 0\n' for a,b,c,d in S)
def ecc(q, toks, Delta):
    try: g = lines(q, toks)
    except ValueError: return None
    r = subprocess.run([HAAR, 'psl', str(q), '1'], input=g, capture_output=True, text=True, timeout=900)
    m = re.search(r'Delta=(\d+) .*compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
    if not m or m.group(5) != 'yes' or m.group(2) != m.group(3): return None
    n, diam = int(m.group(2)), int(m.group(6))
    return diam - math.log(n // 2) / math.log(Delta - 1)
if __name__ == '__main__':
    reps = [tuple(x) for x in json.load(open(os.path.join(HERE, 'orbit_reps.json')))]
    def tok(X): return ':'.join(str(t) for t in X)
    cands = []
    for Delta, nf, no in [(8, 2, 2), (10, 1, 3)]:
        for fixed in itertools.combinations(['I', 'W', 'V'], nf):
            for orbs in itertools.combinations(range(len(reps)), no):
                cands.append((Delta, list(fixed) + [tok(reps[i]) for i in orbs]))
    print('candidates', len(cands), flush=True)
    st1 = []
    for k, (D, toks) in enumerate(cands):
        e = ecc(29, toks, D)
        st1.append({'Delta': D, 'toks': toks, 'e29': e})
        if k % 100 == 0: print('stage1', k, flush=True)
    res = {}
    for D in (8, 10):
        ok = sorted([r for r in st1 if r['Delta'] == D and r['e29'] is not None], key=lambda r: r['e29'])
        print(f'Delta={D} valid at q=29: {len(ok)} of {sum(1 for r in st1 if r["Delta"]==D)}', flush=True)
        top = ok[:40]
        for r in top:
            e41, e53 = ecc(41, r['toks'], D), ecc(53, r['toks'], D)
            r['e41'], r['e53'] = e41, e53
            r['screen_mean'] = None if None in (e41, e53) else round((r['e29'] + e41 + e53) / 3, 4)
        res[D] = top
    json.dump({'stage1': st1, 'top': res}, open(os.path.join(HERE, 'screen_all.json'), 'w'), indent=0)
    for D in (8, 10):
        rows = sorted([r for r in res[D] if r['screen_mean'] is not None], key=lambda r: r['screen_mean'])
        for r in rows[:8]: print(D, r['screen_mean'], round(r['e29'],3), round(r['e41'],3), round(r['e53'],3), ' '.join(r['toks']), flush=True)
    print('DONE', flush=True)
