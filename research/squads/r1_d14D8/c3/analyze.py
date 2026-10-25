"""analyze.py BASE q [nsrc] : structure report for a voltage lift base file (card c3, squad r1_d14D8).
BASE: "N N m" then "p l v" lines; the first N*(q+1) edges are hexagon incidences (sa.c layout), the rest matchings.
Prints voltage histograms, distinct-voltage counts per line, and exact walk statistics of length-7 walks from
point sources (sampled nsrc, or all): walks are split by k = number of matching-edge traversals, and pairs
(point a, line b) are grouped by hexagon distance d(a,b) in {1,3,5}."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, dist_from_point
fn, q = sys.argv[1], int(sys.argv[2])
nsrc = int(sys.argv[3]) if len(sys.argv) > 3 else 40
N, LP, PL, coord = load(q)
with open(fn) as f:
    nA, nB, m = map(int, f.readline().split())
E = np.loadtxt(fn, skiprows=1, dtype=np.int64)
ea, eb, ev = E[:, 0], E[:, 1], E[:, 2] % m
NH = N * (q + 1)
mt = np.zeros(len(ea), dtype=np.int64); mt[NH:] = 1
print(f'base {fn}: N {N} m {m} edges {len(ea)} (hexagon {NH}, matching {len(ea) - NH})')
for name, sl in (('hexagon', slice(0, NH)), ('matching', slice(NH, None))):
    h = np.bincount(ev[sl], minlength=m)
    print(f'  {name} voltages (value:count): ' + ' '.join(f'{g}:{c}' for g, c in enumerate(h)))
    print(f'  {name}: chi2/dof vs uniform {((h - h.mean()) ** 2 / h.mean()).sum() / (m - 1):.2f}')
lv = ev[:NH].reshape(N, q + 1)          # hex edges are grouped by line (LP order)
dist_n = np.array([len(set(r)) for r in lv])
print(f'  hexagon edges per line: mean distinct voltages {dist_n.mean():.2f} of {q + 1}; all distinct: {np.mean(dist_n == q + 1):.3f}')
Lv = np.arange(m)

def transition(cur, src, dst, sh, mtf, ndst):
    """cur (8, nsrc_side, m) -> (8, ndst, m): edge e moves level by sh[e], type k by mtf[e]."""
    E_ = len(src)
    vals = cur[:, src, :]                                     # (8, E, m)
    tl = (Lv[None, :] + sh[:, None]) % m                      # (E, m)
    kk = np.arange(8)[:, None, None] + mtf[None, :, None]     # (8, E, 1)
    valid = np.broadcast_to(kk < 8, (8, E_, m)) & (vals != 0)
    flat = ((np.minimum(kk, 7) * ndst + dst[None, :, None]) * m + tl[None, :, :])
    flat = np.broadcast_to(flat, (8, E_, m))
    out = np.bincount(flat[valid], weights=vals[valid].astype(np.float64), minlength=8 * ndst * m)
    return out.reshape(8, ndst, m)

rng = np.random.default_rng(3)
srcs = np.arange(N) if nsrc >= N else rng.choice(N, nsrc, replace=False)
from collections import defaultdict
agg = defaultdict(list)
hard = []
dsum = np.zeros(3)
tot_walks_k = np.zeros(8)
for s in srcs:
    cur = np.zeros((8, N, m))
    cur[0, s, 0] = 1
    for step in range(7):
        if step % 2 == 0:   # points -> lines, +v
            cur = transition(cur, ea, eb, ev, mt, N)
        else:               # lines -> points, -v
            cur = transition(cur, eb, ea, (m - ev) % m, mt, N)
    W = cur                                                   # (8, N lines, m)
    tot = W.sum(0)                                            # (N, m)
    dp, dl = dist_from_point(s, LP, PL)
    tot_walks_k += W.sum(axis=(1, 2))
    for b in range(N):
        d = int(dl[b])
        if d not in (1, 3, 5):
            continue
        cov = int((tot[b] > 0).sum())
        cov0 = int((W[0, b] > 0).sum())
        cov1 = int((W[1:, b].sum(0) > 0).sum())
        mult = tot[b].min()
        agg[d].append((cov, cov0, cov1, mult))
        if cov < m or mult <= 2:
            g = int(np.argmin(tot[b]))
            hard.append((mult, cov, s, b, d, [int(x) for x in W[:, b, g]]))
print(f'\nsources {len(srcs)}; walk counts by k (matching traversals) summed over sources: '
      + ' '.join(f'k{k}:{int(c)}' for k, c in enumerate(tot_walks_k)))
print('per hexagon distance d(a,b) of the line: pairs | levels covered (all, by k=0, by k>=1) | min mult | uncovered pairs')
for d in (1, 3, 5):
    A_ = np.array(agg[d]) if agg[d] else np.zeros((0, 4))
    if len(A_) == 0:
        continue
    print(f'  d={d}: pairs {len(A_)} | all {A_[:,0].mean():.2f} (min {A_[:,0].min():.0f}) | k0 {A_[:,1].mean():.2f} '
          f'| k>=1 {A_[:,2].mean():.2f} (min {A_[:,2].min():.0f}) | min mult mean {A_[:,3].mean():.1f} '
          f'(min {A_[:,3].min():.0f}) | uncovered pairs {int((A_[:,0] < m).sum())}')
hard.sort(key=lambda t: (t[0], t[1]))
print('hardest (point source a, line b, d, walk counts by k at its least covered level):')
for mult, cov, s, b, d, ks in hard[:6]:
    print(f'  a {s} b {b} d {d}: min mult {int(mult)} covered {cov}/{m}; k-counts {ks}')
# aggregate: levels covered by exactly one walk -> which matching-traversal count k carries it
one = [h for h in hard if h[0] == 1]
kc = np.zeros(8, dtype=np.int64)
for _, _, _, _, _, ks in one:
    kc[int(np.argmax(ks))] += 1
print(f'levels covered by exactly one walk: {len(one)} (over sampled pairs); their k (matching traversals): '
      + ' '.join(f'k{k}:{int(c)}' for k, c in enumerate(kc) if c))
