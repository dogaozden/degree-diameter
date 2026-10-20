"""Pattern of the symmetric exact whisker sets: orbits of G = <x3(s), x1(a)x5(-2a/c), tau> on full S-lines, and the
chosen whisker at each point of one base full S-line, in coordinates.  python3 whisk_pattern.py q"""
import sys
import numpy as np

q = int(sys.argv[1])
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild', '--load']
src = open('hexbig_gf.py').read()
exec(compile(src.split('if build and okfree and okX:')[0], 'hexbig_gf.py', 'exec'))
GENS = [perms(kelem(0, 0, lam)) for lam in basis] + [perms(kelem(lam, 0, 0)) for lam in basis] + [(tp, tl)]
full_set = set(full_lines)
# orbits on full S-lines
seen = {}
for s0 in full_lines:
    if s0 in seen:
        continue
    orb, fr = {s0}, [s0]
    while fr:
        nf = []
        for s in fr:
            for gp, gl in GENS:
                t = int(gl[s])
                if t not in orb:
                    orb.add(t)
                    nf.append(t)
        fr = nf
    for s in orb:
        seen[s] = s0
print('orbits on full S-lines:', len(set(seen.values())), 'sizes', sorted(set(sum(1 for s in seen if seen[s] == r) for r in set(seen.values()))))
Wset = set(W)
base = full_lines[0]
print('base S-line', base, 'points:')
for X in lines[base]:
    X = int(X)
    ks = [int(k) for k in through[X] if int(k) != base]
    toward = [k for k in ks if dist[N + k] == 4]
    w = [k for k in ks if k in Wset]
    def coords(k):
        return [P[int(p)].tolist() for p in lines[k] if int(p) != X][:1]
    print('  X', P[X].tolist(), ' n_X ->', coords(toward[0]), ' whisker ->', coords(w[0]) if w else None,
          ' candidates', len([k for k in ks if dist[N + k] == 6]))
