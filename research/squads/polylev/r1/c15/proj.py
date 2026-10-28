"""c15 (wildcard): algebraic projective colourings of the points of H(q).

A point x (coordinate vector in GF(q)^7) gets the colour [F(x)] in PG(2,q), where F: GF(q)^7 -> GF(q)^3 is
  deg 1: F(x) = M x                       (M a 3 x 7 matrix; linear projection from a solid of PG(6,q))
  deg 2: F(x) = C m(x)                    (C a 3 x 28 matrix; m(x) = all quadratic monomials x_i x_j, i <= j)
Points with F(x) = 0 stay uncoloured. Colour classes are disjoint, so the classes of the good colours are k disjoint
dominating sets as required by the D = 9 lift. A colour c is GOOD when every point 2-ball (the point and its q(q+1)
collinear points) contains a point of colour c. The search is simulated annealing over the entries of M (or C),
minimising the total number of (ball, colour) misses over all q^2+q+1 colours; the score is the number of good colours.

Usage: python3 proj.py HEXBIN deg SEED SECONDS OUTPREFIX
Writes OUTPREFIX.bin (int32 colour per point, -1 = uncoloured, for the best state) and prints the good count.
"""
import sys
import time
import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex  # noqa: E402


class Setup:
    def __init__(self, path):
        H = Hex(path)
        self.H = H
        q, N = H.q, H.N
        self.q, self.N = q, N
        self.X = H.coord.astype(np.int64)
        self.nc = q * q + q + 1
        # 2-ball of each point: the point itself and the q(q+1) points collinear with it
        self.B = np.array([[x] + [y for l in H.PL[x] for y in H.lines[l] if y != x] for x in range(N)], dtype=np.int64)
        # lookup of projective points of PG(2,q): normalised triple -> colour index
        lut = np.full(q ** 3, -1, dtype=np.int64)
        idx = 0
        trip = [(1, a, b) for a in range(q) for b in range(q)] + [(0, 1, a) for a in range(q)] + [(0, 0, 1)]
        self.pg = np.array(trip, dtype=np.int64)
        for t in trip:
            lut[t[0] + q * t[1] + q * q * t[2]] = idx
            idx += 1
        self.lut = lut
        self.w3 = np.array([1, q, q * q], dtype=np.int64)
        # quadratic monomials
        self.mono = [(i, j) for i in range(7) for j in range(i, 7)]
        self.Mq = np.stack([H.MUL[self.X[:, i], self.X[:, j]] for (i, j) in self.mono], axis=1)

    def colour(self, P, deg):
        H = self.H
        if deg == 1:
            Y = H.matvec(P, self.X)
        else:
            Y = H.matvec(P, self.Mq)
        code = Y @ self.w3
        col = np.full(self.N, -1, dtype=np.int64)
        nz = code != 0
        # normalise to first nonzero coordinate = 1
        Yn = H.normalize(Y[nz]) if nz.any() else Y[nz]
        col[nz] = self.lut[Yn @ self.w3]
        return col

    def misses(self, col):
        """number of (ball, colour) pairs with the colour missing from the ball (over colours 0..nc-1)."""
        nc, N = self.nc, self.N
        cb = col[self.B]
        cb = np.where(cb < 0, nc, cb)
        pres = np.zeros((N, nc + 1), dtype=bool)
        rows = np.repeat(np.arange(N), self.B.shape[1]).reshape(N, -1)
        pres[rows, cb] = True
        return int((~pres[:, :nc]).sum()), pres[:, :nc].all(axis=0)


def anneal(S, deg, seed, secs, T0=2.0):
    rng = np.random.default_rng(seed)
    q = S.q
    shape = (3, 7) if deg == 1 else (3, len(S.mono))
    P = rng.integers(0, q, size=shape).astype(np.int64)
    cost, good = S.misses(S.colour(P, deg))
    best = (int(good.sum()), cost, P.copy())
    t0 = time.time()
    it = 0
    T = T0
    while time.time() - t0 < secs:
        it += 1
        i, j = rng.integers(shape[0]), rng.integers(shape[1])
        old = P[i, j]
        new = (old + rng.integers(1, q)) % q
        P[i, j] = new
        c2, g2 = S.misses(S.colour(P, deg))
        d = c2 - cost
        if d <= 0 or rng.random() < np.exp(-d / max(T, 1e-3)):
            cost = c2
            ng = int(g2.sum())
            if ng > best[0] or (ng == best[0] and cost < best[1]):
                best = (ng, cost, P.copy())
        else:
            P[i, j] = old
        T = T0 * (1 - (time.time() - t0) / secs) + 0.05
        if it % 5000 == 0:
            print(f'it {it} cost {cost} good {int(g2.sum())} best {best[0]} T {T:.2f}', flush=True)
    return best, it


def main():
    path, deg, seed, secs, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
    S = Setup(path)
    best, it = anneal(S, deg, seed, secs)
    ng, cost, P = best
    col = S.colour(P, deg)
    # the good colours: relabel so that good colours are 0..k-1 and others uncoloured
    _, good = S.misses(col)
    keep = np.where(good)[0]
    lab = np.full(S.nc, -1, dtype=np.int64)
    lab[keep] = np.arange(len(keep))
    out_col = np.where(col >= 0, lab[np.maximum(col, 0)], -1).astype(np.int32)
    out_col[(col >= 0) & (lab[np.maximum(col, 0)] < 0)] = -1
    out_col.tofile(out + '.bin')
    print(f'DONE q={S.q} deg={deg} seed={seed} iters={it} good={ng} misses={cost} P={P.tolist()}', flush=True)


if __name__ == '__main__':
    main()
