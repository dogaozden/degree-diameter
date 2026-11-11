# holo.py (worker c7b): gauge-invariant holonomies of a cyclic lift of H(q) + J matchings.
# usage: python3 -I holo.py HEXBIN SOLFILE [NPTS] [SEED]
# (1) apartment holonomies: 12-cycles = two geodesics between opposite points (distance 6 in the incidence graph)
#     of the hexagon; holonomy = sum of voltages around the cycle (switching-invariant).
# (2) matching cycles: arc p -> sigma_t(p) (voltage mv_t(p)) closed by a hexagon geodesic back to p.
# Prints value histograms over Z_m (uniform would give 1/m each) and the fraction of zero holonomies.
import sys, random
from collections import Counter, deque
import struct

def load_hex(fn):
    with open(fn, 'rb') as f:
        q, N, L = struct.unpack('<iii', f.read(12))
        pl = struct.unpack('<%di' % (L * (q + 1)), f.read(4 * L * (q + 1)))
    return q, N, [pl[l * (q + 1):(l + 1) * (q + 1)] for l in range(L)]

def load_sol(fn):
    with open(fn) as f:
        q, J, m, D, cost = map(int, f.readline().split())
        f.readline()
        vals = [int(x) for x in f.read().split()]
    return q, J, m, vals

def main():
    hexfn, solfn = sys.argv[1], sys.argv[2]
    npts = int(sys.argv[3]) if len(sys.argv) > 3 else 150
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    q, N, lines = load_hex(hexfn)
    qs, J, m, vals = load_sol(solfn)
    assert qs == q
    Q1 = q + 1
    sig = vals[:J * N]; mv = vals[J * N:2 * J * N]; hv = vals[2 * J * N:]
    # H adjacency: point p -> list of (line, voltage p->line); line l -> list of (point, voltage l->p)
    padj = [[] for _ in range(N)]; ladj = [[] for _ in range(N)]
    for l in range(N):
        for k in range(Q1):
            p = lines[l][k]; w = hv[l * Q1 + k]
            padj[p].append((l, w)); ladj[l].append((p, (-w) % m))
    # 1. apartments
    apt = Counter(); napt = 0
    for _ in range(npts):
        p0 = random.randrange(N)
        # BFS in incidence graph (nodes: ('p',i) / ('l',i)) with all shortest parents
        dist = {('p', p0): 0}; parents = {('p', p0): []}
        frontier = [('p', p0)]
        for d in range(1, 7):
            nxt = []
            for node in frontier:
                side, i = node
                nb = [('l', l) for (l, _) in padj[i]] if side == 'p' else [('p', p) for (p, _) in ladj[i]]
                for nd in nb:
                    if nd not in dist:
                        dist[nd] = d; parents[nd] = [node]; nxt.append(nd)
                    elif dist[nd] == d:
                        parents[nd].append(node)
            frontier = nxt
        opp = [nd for nd in frontier if nd[0] == 'p']
        def paths(nd):
            if nd == ('p', p0): return [[nd]]
            out = []
            for par in parents[nd]:
                for pth in paths(par): out.append(pth + [nd])
            return out
        def wt(a, b):      # voltage of arc a -> b (incidence)
            if a[0] == 'p':
                for (l, w) in padj[a[1]]:
                    if l == b[1]: return w
            else:
                for (p, w) in ladj[a[1]]:
                    if p == b[1]: return w
            raise ValueError
        for z in opp[:6]:
            ps = paths(z)
            if len(ps) < 2: continue
            hol = []
            for pth in ps:
                s = 0
                for a, b in zip(pth, pth[1:]): s += wt(a, b)
                hol.append(s % m)
            for i in range(len(hol)):
                for j in range(i + 1, len(hol)):
                    apt[(hol[i] - hol[j]) % m] += 1; napt += 1
    # 2. matching cycles: p -> sigma(p) then geodesic back to p
    mcyc = Counter(); nm = 0
    for t in range(J):
        for _ in range(npts):
            p0 = random.randrange(N)
            l0 = sig[t * N + p0]; w0 = mv[t * N + p0]
            # BFS from p0 in H to line l0, take one geodesic
            dist = {('p', p0): 0}; par = {('p', p0): None}; dq = deque([('p', p0)])
            while dq:
                nd = dq.popleft()
                if nd == ('l', l0): break
                side, i = nd
                nb = [(('l', l), w) for (l, w) in padj[i]] if side == 'p' else [(('p', p), w) for (p, w) in ladj[i]]
                for (x, w) in nb:
                    if x not in dist:
                        dist[x] = dist[nd] + 1; par[x] = (nd, w); dq.append(x)
            if ('l', l0) not in dist: continue
            s = 0; x = ('l', l0)
            while par[x] is not None:
                pr, w = par[x]; s += w; x = pr
            # the cycle: p0 -> l0 (w0), then back along the geodesic (negated)
            mcyc[(w0 - s) % m] += 1; nm += 1
    def show(name, c, n):
        z = c.get(0, 0) / n if n else float('nan')
        print('%s: samples %d, fraction zero %.4f (uniform 1/m = %.4f), distinct values %d' % (name, n, z, 1.0 / m, len(c)))
    print('q=%d m=%d J=%d' % (q, m, J))
    show('apartment holonomy (hexagon only)', apt, napt)
    show('matching cycle holonomy (p -> sigma p, hexagon geodesic back)', mcyc, nm)
    print('apartment histogram:', [apt.get(v, 0) for v in range(m)])
    print('matching-cycle histogram:', [mcyc.get(v, 0) for v in range(m)])

if __name__ == "__main__":
    main()
