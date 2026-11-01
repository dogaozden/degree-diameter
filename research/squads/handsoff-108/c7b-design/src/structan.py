# structan.py (worker c7b): raw and switching-normalised voltage statistics of a valid lift, and dependence on the
# point coordinates. usage: python3 -I structan.py Q HEXBIN SOLFILE
# normal form: BFS spanning tree of H(q) (incidence graph) with all tree-arc voltages switched to 0;
# the remaining (cotree) hexagon voltages and all matching voltages are then gauge-invariant data.
import sys, math, struct
from collections import Counter, deque
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from holo import load_hex, load_sol  # noqa
q = int(sys.argv[1]); hexfn, solfn = sys.argv[2], sys.argv[3]
q, N, lines = load_hex(hexfn)
qs, J, m, vals = load_sol(solfn)
Q1 = q + 1
sig = vals[:J * N]; mv = vals[J * N:2 * J * N]; hv = vals[2 * J * N:]
with open(hexfn, 'rb') as f:
    f.read(12); f.read(4 * N * Q1); coords = f.read(N * 7)
# raw histograms
raw_h = Counter(hv); raw_m = Counter(mv)
print('q=%d m=%d N=%d' % (q, m, N))
print('raw hexagon voltages (gauge dependent): %d flags, histogram over Z_m: %s' % (len(hv), [raw_h.get(v, 0) for v in range(m)]))
print('raw matching voltages: %d, histogram: %s' % (len(mv), [raw_m.get(v, 0) for v in range(m)]))
# normal form on the hexagon, BFS tree from point 0
padj = [[] for _ in range(N)]; ladj = [[] for _ in range(N)]
for l in range(N):
    for k in range(Q1):
        p = lines[l][k]; w = hv[l * Q1 + k]
        padj[p].append((N + l, w, l * Q1 + k, +1)); ladj[l].append((p, (-w) % m, l * Q1 + k, -1))
pot = {}; tree_arcs = set()
start = ('p', 0); pot[start] = 0; dq = deque([start])
while dq:
    nd = dq.popleft()
    side, i = nd
    if side == 'p':
        for (x, w, f, sgn) in padj[i]:
            y = ('l', x - N)
            if y not in pot:
                pot[y] = (pot[nd] + w) % m; tree_arcs.add(f); dq.append(y)
    else:
        for (p, w, f, sgn) in ladj[i]:
            y = ('p', p)
            if y not in pot:
                pot[y] = (pot[nd] + w) % m; tree_arcs.add(f); dq.append(y)
# switching f = pot: w' = w + f(u) - f(v) on arc u->v; for tree arcs w' = 0 (the potentials were built that way)
nontree = []
for l in range(N):
    for k in range(Q1):
        f = l * Q1 + k
        if f in tree_arcs: continue
        p = lines[l][k]
        w = hv[f] + pot[('p', p)] - pot[('l', l)]
        nontree.append(w % m)
c = Counter(nontree)
print('normal form (BFS tree of H switched to 0): %d cotree hexagon voltages, histogram: %s' %
      (len(nontree), [c.get(v, 0) for v in range(m)]))
# coordinate dependence: mutual information between raw hexagon voltage and point coordinate i (values 0..q-1)
def mi(pairs):
    n = len(pairs); pa = Counter(a for a, b in pairs); pb = Counter(b for a, b in pairs); pab = Counter(pairs)
    return sum((c_ / n) * math.log((c_ / n) / ((pa[a] / n) * (pb[b] / n))) for (a, b), c_ in pab.items())
for coord in range(7):
    pairs = []
    for l in range(N):
        for k in range(Q1):
            p = lines[l][k]
            pairs.append((hv[l * Q1 + k], coords[7 * p + coord]))
    print('MI(raw hexagon voltage ; coordinate %d of its point) = %.4f nats (independent sample bias ~%.4f)' %
          (coord, mi(pairs), (m - 1) * (q - 1) / (2 * len(pairs))))
