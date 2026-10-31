# r2d/grow.py: symmetric growth. From a sigma-invariant cubic bipartite graph (edges file + sigma file, A = 0..m-1,
# B = m..n-1), insert a new fixed pair (a in A, b in B, a~b) by orbit insertion on a free edge orbit {xy, sx sy}:
# remove both edges, add a-y, a-sy, b-x, b-sx, a-b. Output n+2, f+1. Scores every choice with bin/score37.
# usage: grow.py EDGES SIGMA OUTDIR TOPK  -> writes OUTDIR/g<n>_<k>.edges/.sigma for the TOPK best, prints histogram.
import sys, os, subprocess
from collections import Counter
SCORE = '/home/user/degree-diameter/research/squads/handsoff-37/bin/score37'
def load(edges, sigf):
    toks = open(edges).read().split(); n = int(toks[0])
    E = set()
    for i in range(1, len(toks), 2):
        a, b = int(toks[i]), int(toks[i+1]); E.add((min(a, b), max(a, b)))
    sg = list(map(int, open(sigf).read().split()))
    return n, E, sg
def grow_all(n, E, sg):
    m = n // 2
    out = []
    seen = set()
    for (x, y) in sorted(E):          # x in A (< m), y in B (>= m)
        sx, sy = sg[x], sg[y]
        if sg[x] == x or sg[y] == y: continue      # only free orbits (both endpoints non-fixed)
        orb = frozenset([(x, y), (min(sx, sy), max(sx, sy))])
        if orb in seen: continue
        seen.add(orb)
        E2 = [e for e in E if e not in orb]
        a = m; b = n + 1
        X = lambda v: v if v < m else v + 1
        new = [(X(u), X(v)) for (u, v) in E2]
        new += [(a, X(y)), (a, X(sy)), (b, X(x)), (b, X(sx)), (a, b)]
        sg2 = [0] * (n + 2)
        for v in range(n): sg2[X(v)] = X(sg[v])
        sg2[a] = a; sg2[b] = b
        out.append((n + 2, new, sg2))
    return out
def score(n, E, tag, outdir):
    fn = os.path.join(outdir, tag + '.edges')
    with open(fn, 'w') as o:
        o.write(f'{n}\n'); [o.write(f'{u} {v}\n') for (u, v) in E]
    r = subprocess.run([SCORE, fn], capture_output=True, text=True).stdout
    far = int(r.split('far=')[1].split()[0])
    return far, fn
if __name__ == '__main__':
    edges, sigf, outdir, topk = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    os.makedirs(outdir, exist_ok=True)
    n, E, sg = load(edges, sigf)
    cands = grow_all(n, E, sg)
    res = []
    for k, (n2, E2, sg2) in enumerate(cands):
        far, fn = score(n2, E2, f'g{n2}_{k}', outdir)
        sgf = fn[:-6] + '.sigma'
        open(sgf, 'w').write(' '.join(map(str, sg2)) + '\n')
        res.append((far, k, fn))
    res.sort()
    print('n', n + 2, 'candidates', len(res), 'far histogram', sorted(Counter(r[0] for r in res).items())[:12])
    for far, k, fn in res[:topk]: print(far, fn)
