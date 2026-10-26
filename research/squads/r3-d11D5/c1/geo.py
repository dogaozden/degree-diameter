"""Geometry helpers for card c1: W(8) points/lines, hyperbolic PG-lines, regulus, transversals."""
import json, os, sys, itertools, subprocess
D11 = "/home/user/degree-diameter/research/d11D5"
sys.path.insert(0, D11)
os.chdir(D11)
from dcover import load
from w8 import field
n, L, d_pt, d_ln, inv = load(8)
W = json.load(open(os.path.join(D11, "w8.json")))
pts = [tuple(v) for v in W["points"]]
idx = {v: i for i, v in enumerate(pts)}
mul, finv = field(8)
def norm(v):
    for c in v:
        if c:
            s = finv[c]
            return tuple(mul[s][x] for x in v)
def B(x, y):
    return mul[x[0]][y[1]] ^ mul[x[1]][y[0]] ^ mul[x[2]][y[3]] ^ mul[x[3]][y[2]]
def span(i, j):
    x, y = pts[i], pts[j]; s = {i, j}
    for a in range(8):
        v = tuple(x[k] ^ mul[a][y[k]] for k in range(4)); s.add(idx[norm(v)])
    return frozenset(s)
Lsets = [frozenset(s) for s in L]
# collinearity (GQ perp): col[a] = points on a common t.i. line
col = [set() for _ in range(n)]
for s in L:
    for a in s: col[a].update(s)
# hyperbolic PG-lines
hyp = set()
for i in range(n):
    for j in range(i + 1, n):
        if B(pts[i], pts[j]) != 0:
            hyp.add(span(i, j))
hyp = sorted(hyp, key=lambda s: sorted(s))
def regulus_ok(h):
    Ls = [Lsets[d_pt[R]] for R in h]
    return not any(Ls[i] & Ls[j] for i in range(9) for j in range(i + 1, 9))
def transversals(h):
    """t.i. lines (indices into L) meeting all delta(R), R in h, each in exactly one point"""
    Ls = [Lsets[d_pt[R]] for R in h]
    return [t for t in range(n) if all(len(Lsets[t] & Lj) == 1 for Lj in Ls)]
def dominating(X):
    cov = set()
    for y in X: cov |= col[y] | {y}
    return len(cov) == n
def write_in(path, switch, sigma_pts, lstar_pts, lines_override=None):
    """switch: dict line -> (p_removed, x_added) for old lines; lstar_pts: 9 point ids of l*; sigma: list len 586"""
    raise NotImplementedError
def build(lines_pts, sigma, path):
    """lines_pts: list of 586 lists of 9 point ids; sigma: list of 586 line ids"""
    with open(path, "w") as f:
        f.write(f"{len(lines_pts)} 9\n")
        for s in lines_pts: f.write(" ".join(map(str, s)) + "\n")
        for v in sigma: f.write(f"{v}\n")
def score(path, env=None):
    e = dict(os.environ); e["SCORE"] = "1"
    if env: e.update(env)
    out = subprocess.run([PO7, path], env=e, capture_output=True, text=True).stdout
    return out.strip()
PO7 = "/home/user/degree-diameter/research/squads/r3-d11D5/c1/po7"
