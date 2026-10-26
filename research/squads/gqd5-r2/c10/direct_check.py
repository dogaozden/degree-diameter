"""Independent check: every pair of family points has w(x,y) != 0 (no gqlib), and all points are distinct projective points."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'theorems', 'chartlift'))
from gf import GF
from family import family_points

def run(q):
    F = GF(q)
    pts = family_points(q)
    assert len(set(pts)) == len(pts)
    def w(x, y):
        a = F.add[F.mul[x[0]][y[2]]][F.mul[x[1]][y[3]]]
        b = F.add[F.mul[x[2]][y[0]]][F.mul[x[3]][y[1]]]
        return F.sub[a][b]
    bad = sum(1 for i in range(len(pts)) for j in range(i + 1, len(pts)) if w(pts[i], pts[j]) == 0)
    return len(pts), bad

if __name__ == '__main__':
    for q in [int(s) for s in sys.argv[1:]]:
        n, bad = run(q)
        print('q=%d size=%d collinear_pairs=%d' % (q, n, bad), flush=True)
