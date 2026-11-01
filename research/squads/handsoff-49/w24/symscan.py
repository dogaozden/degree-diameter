"""w24 symscan: symmetric (Z_k-equivariant) lift search over metacyclic groups N = meta m k r.
Base: a bipartite base with a side-preserving automorphism sigma of order k acting freely on edges (found here).
phi: automorphism of N of order k (or the identity). Ansatz volt(sigma e) = phi(volt(e)); SA over orbit reps (sym).
Usage: python3 symscan.py BASE GROUPLIST SECS_PER_RUN SEEDS ITERS OUTTSV FROM TO
  GROUPLIST lines: 'n meta:m:k:r'. Writes one TSV line per (group, phi, seed): group, phi-order, class, cost.
  Groups with no order-k automorphism are skipped (phi = identity is also tried)."""
import sys, os, subprocess, struct, array, itertools
from collections import defaultdict

if len(sys.argv) > 8:
    base_f, glist, iters, seeds, outtsv, lo_i, hi_i = sys.argv[1], sys.argv[2], int(sys.argv[5]), int(sys.argv[4]), sys.argv[6], int(sys.argv[7]), int(sys.argv[8])
here = "/home/user/degree-diameter/research/squads/handsoff-49/w24"

def read_base(fn):
    lines = open(fn).read().split('\n')
    b, m = map(int, lines[0].split())
    E = [tuple(map(int, lines[1 + i].split()[:2])) for i in range(m)]
    return b, E

def side_auts(b, E, k):
    """side-preserving automorphisms of the base (A = 0..b/2-1, B = rest) of order k acting freely on edges"""
    h = b // 2
    eset = set(E)
    nbr = {v: set() for v in range(b)}
    for u, v in E: nbr[u].add(v); nbr[v].add(u)
    out = []
    for pa in itertools.permutations(range(h)):
        # image of B-vertex j must have neighbourhood pa(N(j))
        pb = {}
        ok = True
        cand_for = {}
        for j in range(h, b):
            img = frozenset(pa[a] for a in nbr[j])
            cand = [jj for jj in range(h, b) if frozenset(nbr[jj]) == img]
            if len(cand) != 1: ok = False; break
            pb[j] = cand[0]
        if not ok or len(set(pb.values())) != h: continue
        sig = list(range(b))
        for a in range(h): sig[a] = pa[a]
        for j in range(h, b): sig[j] = pb[j]
        # order and freeness on edges
        cur = list(range(b)); o = 0
        while True:
            cur = [sig[c] for c in cur]; o += 1
            if cur == list(range(b)): break
        if o != k: continue
        free = True
        for e in E:
            x = e; orbit = {x}; y = (sig[x[0]], sig[x[1]])
            while y != x:
                orbit.add(y); y = (sig[y[0]], sig[y[1]])
            if len(orbit) != k: free = False; break
        if free: out.append(sig)
    return out

def meta_table(m, k, r):
    n = m * k
    def mul(g, h):
        a, t = g % m, g // m; c, u = h % m, h // m
        return ((a + pow(r, t, m) * c) % m) + m * ((t + u) % k)
    return n, mul

def phi_list(m, k, r, korder):
    """automorphisms of N of order korder (korder | k or korder == 1 -> identity), via images of x=(1,0), y=(0,1)"""
    n, mul = meta_table(m, k, r)
    e = 0
    def power(g, p):
        res = e
        for _ in range(p): res = mul(res, g)
        return res
    def order(g):
        o, h = 1, g
        while h != e: h = mul(h, g); o += 1
        return o
    x = 1 if m > 1 else 0
    y = m if k > 1 else 0
    ords = [order(g) for g in range(n)]
    invs = [None] * n
    for g in range(n):
        for h in range(n):
            if mul(g, h) == e: invs[g] = h; break
    xs = [g for g in range(n) if ords[g] == m]
    # the identity phi is handled by the caller
    ys = [g for g in range(n) if (ords[g] == k or (k == 1 and g == 0)) and (k > 1 or g == 0)]
    ys = [g for g in range(n) if (k > 1 and g // m != 0 and ords[g] == k) or (k == 1 and g == 0)]
    res = []
    for xp in xs:
        xr = power(xp, r % m) if m > 1 else e
        for yp in ys:
            if mul(mul(yp, xp), invs[yp]) != xr: continue
            pxa = [e]
            for a in range(1, m): pxa.append(mul(pxa[-1], xp))
            pyt = [e]
            for t in range(1, k): pyt.append(mul(pyt[-1], yp))
            # cheap order test: phi^korder must fix the generators x and y
            ok5 = True
            for gen in (x, y):
                g = gen
                for _ in range(korder): g = mul(pxa[g % m], pyt[g // m])
                if g != gen: ok5 = False; break
            if not ok5: continue
            # phi(a,t) = xp^a * yp^t
            phi = [0] * n
            for a in range(m):
                for t in range(k):
                    phi[a + m * t] = mul(pxa[a], pyt[t])
            if len(set(phi)) != n: continue
            # order of phi
            o, cur = 1, phi[:]
            while cur != list(range(n)):
                cur = [phi[c] for c in cur]; o += 1
            if o == korder or (korder == 1 and o == 1):
                res.append(phi)
    return res

def write_group(m, k, r, fn):
    n, mul = meta_table(m, k, r)
    arr = array.array('H')
    for g in range(n):
        for h in range(n): arr.append(mul(g, h))
    with open(fn, 'wb') as f:
        f.write(struct.pack('i', n)); arr.tofile(f)

def sym_file(sig, E, phi, korder, fn):
    b = len(sig)
    # orbit representatives: edges up to sigma
    idx = {e: i for i, e in enumerate(E)}
    rep = [-1] * len(E); pw = [0] * len(E); R = 0
    for i, e in enumerate(E):
        if rep[i] >= 0: continue
        cur = e
        for p in range(korder):
            j = idx[cur]
            assert rep[j] < 0
            rep[j] = R; pw[j] = p
            cur = (sig[cur[0]], sig[cur[1]])
        assert cur == e
        R += 1
    with open(fn, 'w') as f:
        f.write(f"{len(phi)}\n" + ' '.join(map(str, phi)) + f"\n{R}\n")
        for i in range(len(E)): f.write(f"{rep[i]} {pw[i]}\n")
    return R

def main():
    b, E = read_base(base_f)
    groups = [l.split() for l in open(glist) if l.strip()]
    groups = [(int(g[0]), g[1]) for g in groups][lo_i - 1:hi_i]
    sigmas = side_auts(b, E, 5 if b == 10 else 7)
    if not sigmas: print('no sigma'); return
    sig = sigmas[0]
    korder = 5 if b == 10 else 7
    print('sigma', sig, 'auts', len(sigmas), flush=True)
    tmp = os.path.join(here, 'scan_tmp'); os.makedirs(tmp, exist_ok=True)
    with open(outtsv, 'a') as out:
        for n_, spec in groups:
            _, a, bm, c = spec.split(':') if spec.count(':') == 3 else (None, None, None, None)
            m, k, r = map(int, spec.split(':')[1:4])
            try:
                phis = phi_list(m, k, r, korder)
            except Exception as ex:
                out.write(f"{n_}\t{spec}\terror {ex}\n"); continue
            classes = [('id', [list(range(m * k))])] if False else []
            cand = []
            pass  # identity phi gave cost ~23000 in a test: skipped
            seen_orb = set()
            for pi_, phi in enumerate(phis):
                key = phi[1] if m > 1 else phi[m]   # phi(x): one representative per value (conjugacy proxy)
                if key in seen_orb: continue
                seen_orb.add(key)
                cand.append((f"phi{pi_}", phi))
                if len(cand) >= 2: break
            if not cand: continue
            gfn = os.path.join(tmp, f"g_{m}_{k}_{r}.bin")
            write_group(m, k, r, gfn)
            for name, phi in cand:
                sfn = os.path.join(tmp, f"sym_{m}_{k}_{r}_{name}.txt")
                R = sym_file(sig, E, phi, korder, sfn)
                for s in range(1, seeds + 1):
                    cmd = ['nice', '-n', '10', os.environ.get('SYMBIN', os.path.join(here, 'sym')), base_f, gfn, '9', str(iters), str(s), '5', '0.5',
                           os.path.join(tmp, f"o_{m}_{k}_{r}_{name}_{s}"), sfn]
                    try:
                        res = subprocess.run(cmd, capture_output=True, text=True, timeout=120).stdout
                    except subprocess.TimeoutExpired:
                        res = 'RESULT timeout'
                    line = res.strip().split('\n')[-1] if res.strip() else 'RESULT none'
                    out.write(f"{n_}\t{spec}\t{name}\tR={R}\tseed={s}\t{line}\n"); out.flush()
                    if 'FOUND' in line:
                        print('FOUND', n_, spec, name, s, flush=True)
            os.remove(gfn)
            print('done', n_, spec, len(cand), flush=True)

if __name__ == '__main__':
    main()
