#!/usr/bin/env python3
"""sym.py: symmetric (cyclic-group-invariant) freed-flag sets for the exact-coverage matching (flagmatch.py rules).
Elements of PGSp(4,7) are built from random transvections (and diag(1,l,1,l) similitudes), acting on the gq bin.
usage: python3 -I sym.py gq/gq_q7.bin SEED TRIES MODE(any|far) [ORDERS e.g. 5,8,10] [ELEMS]"""
import sys, random, struct, math, os
sys.path.insert(0, '.')
from gq import perp, lperp
Q = 7
J = [[0, 1, 0, 0], [6, 0, 0, 0], [0, 0, 0, 1], [0, 0, 6, 0]]   # B(x,y) = x0y1-x1y0+x2y3-x3y2 = x^T J y

def load_all(fn):
    d = open(fn, 'rb').read()
    q, N, L = struct.unpack('3i', d[:12]); Q1 = q + 1; off = 12; lines = []
    for _ in range(L):
        lines.append(list(struct.unpack(f'{Q1}i', d[off:off + 4 * Q1]))); off += 4 * Q1
    coords = [tuple(d[off + 7 * i + j] for j in range(4)) for i in range(N)]
    lof = [[] for _ in range(N)]
    for l, ps in enumerate(lines):
        for p in ps: lof[p].append(l)
    return q, N, lines, lof, coords

def normalize(w):
    for x in w:
        if x:
            s = pow(x, 5, Q)                         # x^-1 mod 7
            return tuple((s * y) % Q for y in w)
    raise ValueError('zero vector')

def matmul(A, B): return [[sum(A[i][k] * B[k][j] for k in range(4)) % Q for j in range(4)] for i in range(4)]
def transpose(A): return [list(r) for r in zip(*A)]
def sim_lambda(M):
    T = matmul(matmul(transpose(M), J), M); lam = T[0][1]
    if lam == 0: return None
    for i in range(4):
        for j in range(4):
            if T[i][j] != (lam * J[i][j]) % Q: return None
    return lam

def transvection(v, c):
    Jv = [sum(J[j][k] * v[k] for k in range(4)) % Q for j in range(4)]
    return [[((1 if i == j else 0) + c * v[i] * Jv[j]) % Q for j in range(4)] for i in range(4)]

def random_elem(rng):
    M = [[int(i == j) for j in range(4)] for i in range(4)]
    for _ in range(rng.randint(6, 14)):
        v = [rng.randrange(Q) for _ in range(4)]
        if not any(v): continue
        M = matmul(M, transvection(v, rng.randint(1, Q - 1)))
    if rng.random() < 0.5:                      # similitude diag(1,l,1,l)
        lam = rng.randint(2, Q - 1); M = matmul(M, [[1, 0, 0, 0], [0, lam, 0, 0], [0, 0, 1, 0], [0, 0, 0, lam]])
    return M

def perm_points(M, coords, index):
    out = []
    for v in coords:
        w = [sum(M[r][k] * v[k] for k in range(4)) % Q for r in range(4)]
        out.append(index[normalize(w)])
    return out

def perm_lines(pp, lines, lidx):
    return [lidx[frozenset(pp[p] for p in lines[l])] for l in range(len(lines))]

def cycle_type(perm):
    seen = [False] * len(perm); ct = {}
    for i in range(len(perm)):
        if not seen[i]:
            c = 0; j = i
            while not seen[j]: seen[j] = True; j = perm[j]; c += 1
            ct[c] = ct.get(c, 0) + 1
    return ct

def order_of(ct):
    o = 1
    for c in ct: o = o * c // math.gcd(o, c)
    return o

def flag_orbits(pp, pl, flags):
    seen = set(); orbits = []
    for f in flags:
        if f in seen: continue
        orb = []; g = f
        while g not in seen:
            seen.add(g); orb.append(g); g = (pp[g[0]], pl[g[1]])
        orbits.append(orb)
    return orbits

class Matcher:
    def __init__(self, q, N, lines, lof):
        self.N = N; self.lines = lines
        self.Pm = [sum(1 << y for y in perp(lines, lof, p)) for p in range(N)]
        self.Lm = [sum(1 << m for m in lperp(lines, lof, l)) for l in range(N)]
        self.onl = [sum(1 << y for y in lines[l]) for l in range(N)]
        self.thr = [sum(1 << m for m in lof[p]) for p in range(N)]
        self.ALL = (1 << N) - 1
    def size(self, flags):
        N = self.N; Pm, Lm, onl, thr, ALL = self.Pm, self.Lm, self.onl, self.thr, self.ALL
        F = {p: l for p, l in flags}; Fl = {l for p, l in flags}
        Fm = sum(1 << p for p in F); Flm = sum(1 << l for l in Fl)
        lineok = [ALL & ~Flm] * N; ptok = [ALL & ~Fm] * N
        for p, l in flags:
            A = Pm[p] & ~onl[l]; G = Lm[l] & ~thr[p]; Ll = Lm[l] & ~(1 << l); Pp = Pm[p] & ~(1 << p)
            x = A
            while x:
                b = x & -x; i = b.bit_length() - 1; lineok[i] &= Ll; x ^= b
            m = G
            while m:
                b = m & -m; i = b.bit_length() - 1; ptok[i] &= Pp; m ^= b
        adj = []
        for x in range(N):
            if x in F: adj.append([F[x]]); continue
            row = []; m = lineok[x]
            while m:
                b = m & -m; M = b.bit_length() - 1; m ^= b
                if ptok[M] >> x & 1: row.append(M)
            adj.append(row)
        matchR = [-1] * N; matchL = [-1] * N
        sys.setrecursionlimit(20000)
        def aug(u, seen):
            for v in adj[u]:
                if v in seen: continue
                seen.add(v)
                if matchR[v] < 0 or aug(matchR[v], seen):
                    matchR[v] = u; matchL[u] = v; return True
            return False
        for x in F:
            M = F[x]; matchR[M] = x; matchL[x] = M
        for u in range(N):
            if matchL[u] < 0: aug(u, set())
        return sum(1 for u in range(N) if matchL[u] >= 0), matchL

def greedy(orbits, rng, mode, M, N, Pm, Lm):
    order = list(range(len(orbits))); rng.shuffle(order)
    FP = set(); FL = set(); flags = []
    for oi in order:
        orb = orbits[oi]
        ps = [p for p, l in orb]; ls = [l for p, l in orb]
        if len(set(ps)) < len(ps) or len(set(ls)) < len(ls): continue
        if FP.intersection(ps) or FL.intersection(ls): continue
        if mode == 'far':
            bad = False
            for p, l in orb:
                for f, g in flags:
                    if Pm[p] >> f & 1 or Lm[l] >> g & 1: bad = True; break
                if bad: break
                for p2, l2 in orb:
                    if p2 != p and (Pm[p] >> p2 & 1 or Lm[l] >> l2 & 1): bad = True; break
                if bad: break
            if bad: continue
        cand = flags + orb
        sz, _ = M.size(cand)
        if sz == N:
            flags = cand; FP.update(ps); FL.update(ls)
    return flags

if __name__ == '__main__':
    fn = sys.argv[1]; seed = int(sys.argv[2]); tries = int(sys.argv[3]); mode = sys.argv[4]
    orders = set(map(int, sys.argv[5].split(','))) if len(sys.argv) > 5 else {5, 8, 10}
    nel = int(sys.argv[6]) if len(sys.argv) > 6 else 400
    rng = random.Random(seed)
    q, N, lines, lof, coords = load_all(fn)
    index = {c: i for i, c in enumerate(coords)}
    lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
    M = Matcher(q, N, lines, lof)
    flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]
    print('W(%d) N=%d L=%d flags=%d' % (q, N, len(lines), len(flags_all)), flush=True)
    seen_ct = {}
    best = {}
    for e in range(nel):
        Mx = random_elem(rng)
        lam = sim_lambda(Mx)
        if lam is None: print('not similitude!'); sys.exit(1)
        pp = perm_points(Mx, coords, index)
        ct = cycle_type(pp); o = order_of(ct)
        if o not in orders: continue
        key = (o, tuple(sorted(ct.items())))
        if key in seen_ct: continue
        seen_ct[key] = 1
        pl = perm_lines(pp, lines, lidx)
        orbs = flag_orbits(pp, pl, flags_all)
        osz = {}
        for ob in orbs: osz[len(ob)] = osz.get(len(ob), 0) + 1
        print('ELEM order', o, 'pts cycles', sorted(ct.items()), 'flag orbit sizes', sorted(osz.items()), 'lambda', lam, flush=True)
        bestk = 0; bestset = None
        for t in range(tries):
            fl = greedy(orbs, rng, mode, M, N, M.Pm, M.Lm)
            if len(fl) > bestk: bestk = len(fl); bestset = fl
            print('  run', t, 'k', len(fl), flush=True)
        print('BEST order', o, 'k', bestk, 'flags', bestset, flush=True)
        if bestk >= 6:
            print('FOUND_K6PLUS', bestk, flush=True)
