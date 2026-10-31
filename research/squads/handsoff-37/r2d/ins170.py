# r2d/ins170.py: equivariant insertion of a fixed edge (a,b) into C168.1 for each colour-preserving FREE involution.
# old A = 0..83, old B = 84..167 -> new numbering: A stays, B shifts by +1; new a = 84 (A), new b = 169 (B).
# Orbit insertion: remove edge orbit {x y, sx sy} (x in A, y in B), add a-y, a-sy, b-x, b-sx, a-b. Result: n=170, f=1.
import pickle, subprocess, sys, os
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
n0, m0 = 168, 84
E0 = []
toks = open('/home/user/degree-diameter/research/squads/handsoff-37/shared/seeds/conder168.edges').read().split()
for i in range(1, len(toks), 2): E0.append((int(toks[i]), int(toks[i+1])))
def shift(v): return v if v < m0 else v + 1
invs = pickle.load(open(os.path.join(HERE, 'out/c168_colour_invols.pkl'), 'rb'))
res = []
for ci, (col, fv, fe, p) in enumerate(invs):
    Es = set(tuple(sorted((a, b))) for a, b in E0)
    seen = set(); k = 0
    for (x0, y0) in E0:
        x, y = (x0, y0) if x0 < m0 else (y0, x0)   # x in A, y in B
        orb = frozenset([(x, y), (p[x], p[y])])
        if orb in seen: continue
        seen.add(orb)
        sx, sy = p[x], p[y]
        E = [e for e in Es if e != tuple(sorted((x, y))) and e != tuple(sorted((sx, sy)))]
        a, b = 84, 169
        X = lambda v: shift(v)
        new = [(X(v), X(w)) for (v, w) in E]
        new += [(a, X(y)), (a, X(sy)), (b, X(x)), (b, X(sx)), (a, b)]
        name = os.path.join(HERE, 'out', f'ins170_inv{ci}_{k}.edges')
        with open(name, 'w') as o:
            o.write('170\n'); [o.write(f'{u} {v}\n') for (u, v) in new]
        # sigma on new numbering
        sg = [0] * 170
        for v in range(n0):
            sg[X(v)] = X(p[v])
        sg[a] = a; sg[b] = b
        with open(os.path.join(HERE, 'out', f'ins170_inv{ci}_{k}.sigma'), 'w') as o:
            o.write(' '.join(map(str, sg)) + '\n')
        out = subprocess.run(['/home/user/degree-diameter/research/squads/handsoff-37/bin/score37', name], capture_output=True, text=True).stdout.strip()
        far = int(out.split('far=')[1].split()[0])
        res.append((far, ci, k, name, out))
        k += 1
res.sort()
print('insertions', len(res))
print('far histogram (lowest 10):', [r[0] for r in res[:10]])
print('far distribution:', sorted(Counter(r[0] for r in res).items())[:15])
for r in res[:3]: print(r[4], r[3])
