"""Wildcard test: level graphs on L levels where some level pairs are NOT joined by a matching.
Each level j: A-side ext out-degree <= e, B-side ext in-degree <= e (degree q+1+e).  Random orientation of a random
subset of level pairs, random types and random bijections; checked with the all-pairs BFS apsp (D = 5)."""
import sys, os, random, subprocess, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
APSP = '/home/user/degree-diameter/research/theorems/d5gq/apsp'

def random_arcs(L, e, rng, target):
    """random orientation of pairs, out<=e, in<=e, greedily; returns list of (j,j2)"""
    pairs = list(itertools.combinations(range(L), 2)); rng.shuffle(pairs)
    out = [0]*L; inn = [0]*L; arcs = []
    for a, b in pairs:
        if len(arcs) >= target: break
        opts = []
        if out[a] < e and inn[b] < e: opts.append((a, b))
        if out[b] < e and inn[a] < e: opts.append((b, a))
        if opts:
            x, y = rng.choice(opts); arcs.append((x, y)); out[x] += 1; inn[y] += 1
    return arcs

def build_graph(G, types, arcs, rng):
    L = len(types); per = G.np + G.nl; edges = []
    for j in range(L):
        for l, pts in enumerate(G.lines):
            for p in pts: edges.append((j*per + p, j*per + G.np + l))
    for (j, j2) in arcs:
        # A-elements of level j: points if H else lines; B-elements of level j2: lines if H else points
        A = list(range(G.np)) if types[j] == 'H' else list(range(G.np, per))
        B = list(range(G.np, per)) if types[j2] == 'H' else list(range(G.np))
        perm = B[:]; rng.shuffle(perm)
        for a, b in zip(A, perm): edges.append((j*per + a, j2*per + b))
    return L*per, edges

def check(n, edges, d, path):
    with open(path, 'w') as f:
        f.write('%d\n' % n); f.write(''.join('%d %d\n' % e for e in edges))
    out = subprocess.run([APSP, path, str(d), '5'], capture_output=True, text=True).stdout.strip()
    return ('RESULT VALID' in out), out

if __name__ == '__main__':
    q, e, L, trials, seed = map(int, sys.argv[1:6])
    G = gqlib.W(q); rng = random.Random(seed)
    best = None; npass = 0; arcs_max = L*e
    for t in range(trials):
        types = [rng.choice('HD') for _ in range(L)]
        arcs = random_arcs(L, e, rng, arcs_max)
        n, edges = build_graph(G, types, arcs, rng)
        ok, out = check(n, edges, q+1+e, '/home/user/degree-diameter/research/squads/gqd5-r1/c18/tmp_%d_%d_%d.txt' % (q, L, seed))
        if ok:
            npass += 1
            if best is None: best = (types, arcs, n, edges)
    print('q=%d e=%d L=%d arcs=%d pairs=%d trials=%d pass=%d' % (q, e, L, len(arcs), L*(L-1)//2, trials, npass))
    if best:
        print('example types', best[0], 'arcs', best[1], 'n', best[2], 'deg', q+1+e)
