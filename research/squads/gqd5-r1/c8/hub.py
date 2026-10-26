"""Hub scheme for the 3-level test bed.  R = freed points of L1 (transition 1->2).
B-hub h_y: joined to (y,1) (its only spare slot), one per y in R.
A-hub g_w: joined to (w,2), one per w in R.
Y: h_y ~ g_w iff y, w in R are collinear (y != w)  [the 'double cover' of the collinearity graph of R].
Degrees: h_y, g_w have 1 + deg_R(.) <= q+2 iff collinearity degree in R <= q+1."""
import sys, subprocess; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from base import *
APSP='/home/user/degree-diameter/research/theorems/d5gq/apsp'

def hub_edges(G, R, M01):
    R = sorted(set(R))
    n0, E, per = base_edges(G, M01, R)
    idx = {y: i for i, y in enumerate(R)}
    nB = len(R)
    Bv = lambda y: n0 + idx[y]
    Av = lambda w: n0 + nB + idx[w]
    for y in R:
        E.append((Bv(y), 1 * per + y))
        E.append((Av(y), 2 * per + y))
    Ys = []
    for y in R:
        for w in R:
            if y != w and G.col[y, w]:
                E.append((Bv(y), Av(w))); Ys.append((y, w))
    n = n0 + 2 * nB
    return n, E, per, Ys

def check(G, R, M01, q, label=''):
    n, E, per, Ys = hub_edges(G, R, M01)
    deg = np.zeros(n, dtype=int)
    for a, b in E: deg[a] += 1; deg[b] += 1
    p = '/home/user/degree-diameter/research/squads/gqd5-r1/c8/tmp_hub_%s.txt' % label
    write(p, n, E)
    out = subprocess.run([APSP, p, str(q + 2), '5'], capture_output=True, text=True).stdout.strip().splitlines()[-1]
    dn, dg = diam_numpy(n, E)
    return out, 'numpy diam', dn, 'maxdeg', int(deg.max()), '|R|', len(R), '|Y|', len(Ys)

if __name__ == '__main__':
    q = int(sys.argv[1])
    G = getG(q); M = random_M01(G, 1)
    x = 0; s = G.plines[0][0]; y = [p2 for p2 in G.lines[s] if p2 != x][0]
    print('collinear pair with hubs:', check(G, [x, y], M, q, 'pair%d' % q))
    z = [p2 for p2 in range(G.np) if not G.col[x, p2] and p2 != x][0]
    print('noncollinear pair with hubs:', check(G, [x, z], M, q, 'nc%d' % q))
