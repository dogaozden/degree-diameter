import sys; sys.path.insert(0,'/home/user/degree-diameter/research/squads/gqd5-r1/c8')
from hub import *
from bad import dist_matrix
from collections import Counter
def lab(v, n0, per, G, R, nB):
    if v < n0:
        j = v // per; e = v % per
        return ('L%d' % j) + ('p%d' % e if e < G.np else 'l%d' % (e - G.np))
    k = v - n0
    if k < nB: return 'h_B(%d)' % sorted(R)[k]
    return 'h_A(%d)' % sorted(R)[k - nB]
if __name__ == '__main__':
    q = int(sys.argv[1]); G = getG(q); M = random_M01(G, 1)
    x = 0; s = G.plines[0][0]; y = [p2 for p2 in G.lines[s] if p2 != x][0]
    R = [x, y]
    n, E, per, Ys = hub_edges(G, R, M)
    D = dist_matrix(n, E)
    n0 = 3 * per
    bad = np.argwhere(D > 5)
    print('max dist', D.max(), 'bad unordered', sum(1 for a, b in bad if a < b))
    for a, b in bad:
        if a < b:
            print(lab(a, n0, per, G, R, len(R)), lab(b, n0, per, G, R, len(R)), D[a, b])
