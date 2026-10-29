#!/usr/bin/env python3
"""Card c3 (round d7thm-r1): checks of the q-even sets of research/squads/d7thm-r1/BRIEF.md.

usage: python3 even_checks.py q [own|hexgen]
  own    : H(q) built here from the quadric and Tits' six Pluecker equations (q=2,4)
  hexgen : H(q) read from hex/hex_q{q}.bin written by hexgen2; every stored point and line is re-verified
           with this file's own GF(q) arithmetic (q=8).
GF(q) = GF(2)[x]/(m(x)), element a0 + 2 a1 + 4 a2 + ..., m = x^2+x+1, x^3+x+1, x^4+x+1 for q=4,8,16.
The W / S_0 / R_L / P_S checks are repeated for every zero-free pair (c0,c1); the first pair is reported in full.
"""
import sys, os, struct, itertools, io, contextlib
import numpy as np

q = int(sys.argv[1])
src = sys.argv[2] if len(sys.argv) > 2 else ('own' if q <= 4 else 'hexgen')
HERE = os.path.dirname(os.path.abspath(__file__))
K = {2: 1, 4: 2, 8: 3, 16: 4}[q]
MODP = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011}[K]

def rawmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if (a >> K) & 1:
            a ^= MODP
    return r

MUL = np.array([[rawmul(a, b) for b in range(q)] for a in range(q)], dtype=np.int64)
ML = MUL.tolist()
INV = [0] * q
for a in range(1, q):
    for b in range(1, q):
        if ML[a][b] == 1:
            INV[a] = b
INVA = np.array(INV, dtype=np.int64)
results = []

def check(label, ok, detail=""):
    results.append((label, bool(ok), detail))
    print(("PASS " if ok else "FAIL ") + label + ("  [" + detail + "]" if detail else ""), flush=True)

fld_ok = all(ML[a][ML[b][c]] == ML[ML[a][b]][c] for a in range(q) for b in range(q) for c in range(q))
fld_ok &= all(ML[a][b ^ c] == (ML[a][b] ^ ML[a][c]) for a in range(q) for b in range(q) for c in range(q))
fld_ok &= all(ML[a][INV[a]] == 1 for a in range(1, q))
check("F0 GF(%d) arithmetic: associative, distributive, inverses" % q, fld_ok)

def normvec(v):
    for c in v:
        if c:
            i = INV[c]
            break
    return tuple(ML[i][x] for x in v)

def Qf(x):
    return ML[x[0]][x[4]] ^ ML[x[1]][x[5]] ^ ML[x[2]][x[6]] ^ ML[x[3]][x[3]]

def Bf(x, y):
    return (ML[x[0]][y[4]] ^ ML[x[4]][y[0]] ^ ML[x[1]][y[5]] ^ ML[x[5]][y[1]]
            ^ ML[x[2]][y[6]] ^ ML[x[6]][y[2]])

def tits(x, y):
    def p(i, j):
        return ML[x[i]][y[j]] ^ ML[x[j]][y[i]]   # minus = plus in characteristic 2
    return (p(1, 2) == p(3, 4) and p(5, 4) == p(3, 2) and p(2, 0) == p(3, 5)
            and p(6, 5) == p(3, 0) and p(0, 1) == p(3, 6) and p(4, 6) == p(3, 1))

def trace(x):
    t, y = 0, x
    for _ in range(K):
        t ^= y
        y = ML[y][y]
    return t

# ---------- build H(q) ----------
if src == 'own':
    seen, P = set(), []
    for v in itertools.product(range(q), repeat=7):
        if not any(v):
            continue
        nv = normvec(v)
        if nv in seen:
            continue
        seen.add(nv)
        if Qf(nv) == 0:
            P.append(nv)
    idx = {p: i for i, p in enumerate(P)}
    N = len(P)
    lineset = set()
    for i in range(N):
        x = P[i]
        for j in range(i + 1, N):
            y = P[j]
            if Bf(x, y) != 0 or not tits(x, y):
                continue
            Lp = {i}
            for t in range(q):
                w = normvec(tuple(y[k] ^ ML[t][x[k]] for k in range(7)))
                Lp.add(idx[w])
            lineset.add(tuple(sorted(Lp)))
    lines = sorted(lineset)
    print("built H(%d) from the quadric and Tits equations: %d points, %d lines" % (q, N, len(lines)))
else:
    path = os.path.join(HERE, 'hex', 'hex_q%d.bin' % q)
    data = open(path, 'rb').read()
    qq, N, Lc = struct.unpack('<3i', data[:12])
    assert qq == q
    lid = np.frombuffer(data, dtype='<i4', count=Lc * (q + 1), offset=12).reshape(Lc, q + 1)
    off = 12 + 4 * Lc * (q + 1)
    co = np.frombuffer(data, dtype=np.uint8, count=N * 7, offset=off).reshape(N, 7)
    check("H0 hexgen2 file size matches header (N=%d, L=%d)" % (N, Lc), off + 7 * N == len(data))
    raw = [tuple(int(c) for c in row) for row in co]
    P = [normvec(v) for v in raw]
    nonnorm = sum(1 for a, b in zip(raw, P) if a != b)
    idx = {p: i for i, p in enumerate(P)}
    check("H0a stored point rows distinct after normalising", len(idx) == N, "non-normalised rows: %d" % nonnorm)
    lines = [tuple(sorted(int(v) for v in row)) for row in lid]
    print("read H(%d) from hexgen2: %d points, %d lines" % (q, N, len(lines)))

N = len(P)
L = len(lines)
PA = np.array(P, dtype=np.int64)
check("H1 every stored point satisfies Q=0 (own arithmetic); N=%d" % N, all(Qf(p) == 0 for p in P),
      "(q^6-1)/(q-1) = %d" % ((q ** 6 - 1) // (q - 1)))
check("H2 N = (q^6-1)/(q-1) points and N lines", N == (q ** 6 - 1) // (q - 1) and L == N,
      "points %d, lines %d" % (N, L))
okl, bad = True, ""
for l, pl in enumerate(lines):
    if len(set(pl)) != q + 1:
        okl, bad = False, "line %d size" % l
        break
    pts = [P[i] for i in pl]
    x, y = pts[0], pts[1]
    if not tits(x, y):
        okl, bad = False, "Tits fails on line %d" % l
        break
    if any(Bf(a, b) != 0 for a, b in itertools.combinations(pts, 2)) or any(Qf(a) for a in pts):
        okl, bad = False, "not totally singular on line %d" % l
        break
    span = {pl[0]} | {idx[normvec(tuple(y[k] ^ ML[t][x[k]] for k in range(7)))] for t in range(q)}
    if span != set(pl):
        okl, bad = False, "not the span of two of its points, line %d" % l
        break
check("H3 each line: q+1 points, totally singular, Tits equations, equals span of two of its points", okl, bad)
ppl = [0] * N
for pl in lines:
    for p in pl:
        ppl[p] += 1
check("H4 every point on exactly q+1 lines", all(c == q + 1 for c in ppl))

pt_lines = [[] for _ in range(N)]
for l, pl in enumerate(lines):
    for p in pl:
        pt_lines[p].append(l)
adj = [[] for _ in range(N + L)]
for l, pl in enumerate(lines):
    for p in pl:
        adj[p].append(N + l)
        adj[N + l].append(p)

def bfs(src_node, maxd=99):
    dist = [-1] * (N + L)
    dist[src_node] = 0
    frontier, d = [src_node], 0
    while frontier and d < maxd:
        d += 1
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = d
                    nxt.append(w)
        frontier = nxt
    return dist

d0 = bfs(0)
layers = [sum(1 for x in d0 if x == k) for k in range(7)]
want = [1, q + 1, q * q + q, q ** 3 + q * q, q ** 4 + q ** 3, q ** 5 + q ** 4, q ** 5]
check("H5 incidence-graph distance layers from a point = hexagon of order (q,q)", layers == want,
      "layers %s" % layers)

# ---------- the sets ----------
X = [PA[:, k] for k in range(7)]
pid = lambda vec: idx[normvec(vec)]
e1 = pid((0, 1, 0, 0, 0, 0, 0))
e6 = pid((0, 0, 0, 0, 0, 0, 1))
v = (set(pt_lines[e1]) & set(pt_lines[e6])).pop()
check("S0 v = line through e1, e6 is a line of H(q)", set(lines[v]) >= {e1, e6})
dv = bfs(N + v)
pts_v = np.array([dv[p] for p in range(N)])

deltas = [d for d in range(q) if trace(d) == 1]
DEL = deltas[0] if deltas else -1
check("C1a delta with absolute trace 1 exists (Tr = x + x^2 + ... + x^(q/2))", len(deltas) == q // 2,
      "%d such delta, first delta=%d" % (len(deltas), DEL))

def Gval(c0, c1, a, b):
    lin = ML[c0][a] ^ ML[c1][b]
    quad = ML[a][a] ^ ML[a][b] ^ ML[DEL][ML[b][b]]
    return ML[lin][quad] ^ ML[b][ML[b][b]]

good = [(c0, c1) for c0 in range(q) for c1 in range(q)
        if all(Gval(c0, c1, a, b) != 0 for a in range(q) for b in range(q) if (a, b) != (0, 0))]
check("C1b G zero-free on F^2\\{0} for some (c0,c1)  (Lemma: yes for q>=4; q=2: must be no)",
      (len(good) > 0) if q >= 4 else (len(good) == 0),
      "%d of %d pairs (c0,c1) work" % (len(good), q * q))

L0 = X[0] ^ MUL[DEL][X[4]] ^ X[3]            # Pi: X3 = X0 + delta X4 (plus alpha X2 + beta X5 for Pi_z)
PiMask = (L0 == 0)
LA = np.array(lines, dtype=np.int64)
check("C1c Pi cap H(q) has (q+1)(q^3+1) points", int(PiMask.sum()) == (q + 1) * (q ** 3 + 1),
      "%d" % int(PiMask.sum()))
S_ids = np.nonzero(PiMask[LA].all(axis=1))[0].tolist()
check("C1d S = lines of H(q) in Pi: q^3+1 lines", len(S_ids) == q ** 3 + 1, "|S| = %d" % len(S_ids))
check("C1e v in S", v in set(S_ids))

def opposite_all(group):
    for l in group:
        dl = bfs(N + l, maxd=4)
        for m in group:
            if m != l and dl[N + m] >= 0:
                return False
    return True
check("C1f S pairwise opposite (incidence distance 6)", opposite_all(S_ids))

near = {p for p in range(N) if pts_v[p] in (1, 3)}
xs0 = {p for p in range(N) if X[2][p] == 0 and X[5][p] == 0}
check("C1g points at distance <= 3 from v are exactly the points with X2 = X5 = 0", near == xs0,
      "|dist<=3| = %d, |X2=X5=0| = %d" % (len(near), len(xs0)))
free = [p for p in range(N) if pts_v[p] == 5 and not PiMask[p]]
check("C1h free points (not in Pi, distance 5 from v) number q^3(q^2-1)", len(free) == q ** 3 * (q * q - 1),
      "%d vs %d" % (len(free), q ** 3 * (q * q - 1)))
Lv = sorted({l for p in lines[v] for l in pt_lines[p] if l != v})
check("C1i L_v = q(q+1) lines != v meeting v", len(Lv) == q * (q + 1), "%d" % len(Lv))

numP = MUL[X[2], X[3]] ^ MUL[X[2], X[4]] ^ MUL[X[4], X[5]]
denP = MUL[DEL][MUL[X[2], X[2]]] ^ MUL[X[2], X[5]] ^ MUL[X[5], X[5]]
nuP = np.where(denP != 0, MUL[numP, INVA[denP]], -1)
Sv = [l for l in S_ids if l != v]

def run_pair(C0, C1):
    """All checks that depend on the choice of (c0,c1). Appends to results."""
    Wmult = {}
    wrong_pi = 0
    undefined = 0
    for al in range(q):
        for be in range(q):
            if al == 0 and be == 0:
                continue
            Lz = L0 ^ MUL[al][X[2]] ^ MUL[be][X[5]]
            zmask = (Lz == 0)
            Sz = np.nonzero(zmask[LA].all(axis=1))[0].tolist()
            den = ML[al][al] ^ ML[al][be] ^ ML[DEL][ML[be][be]]
            Fz = ML[Gval(C0, C1, al, be)][INV[den]]
            for l in Sz:
                if l == v:
                    continue
                if PiMask[LA[l]].all():
                    wrong_pi += 1
                    continue
                pt = [p for p in lines[l] if PiMask[p]][0]
                if denP[pt] == 0:
                    undefined += 1
                    continue
                if nuP[pt] == Fz:
                    Wmult[l] = Wmult.get(l, 0) + 1
    W = sorted(Wmult)
    Wset = set(W)
    check("W1 |W| = q^2(q^2-1)  (lines of S_z, != v, with nu(meet Pi) = F(z), z != 0)",
          len(W) == q * q * (q * q - 1), "|W| = %d, want %d; W lines in Pi excluded: %d; nu undefined: %d; "
          "max #z per line: %d" % (len(W), q * q * (q * q - 1), wrong_pi, undefined,
                                   max(Wmult.values()) if Wmult else 0))
    freeS = set(free)
    cnt = {}
    for p in free:
        c = sum(1 for l in pt_lines[p] if l in Wset)
        cnt[c] = cnt.get(c, 0) + 1
    check("W2 each free point on exactly one W line", cnt == {1: len(free)}, "W-line counts over free points: %s" % cnt)
    wpt = {}
    for l in W:
        for p in lines[l]:
            if PiMask[p]:
                wpt[p] = wpt.get(p, 0) + 1
    const_bad = 0
    den_bad = 0
    nu_of, meet = {}, {}
    for m in Sv:
        vals = set(int(nuP[p]) for p in lines[m])
        if len(vals) != 1:
            const_bad += 1
        if any(denP[p] == 0 for p in lines[m]):
            den_bad += 1
        nu_of[m] = int(nuP[lines[m][0]])
        meet[m] = sum(wpt.get(p, 0) for p in lines[m])
    check("N1 nu defined and constant on each spread line != v", const_bad == 0 and den_bad == 0,
          "non-constant: %d; with X2=X5=0 point: %d" % (const_bad, den_bad))
    ok_meet = all(meet[m] == 0 or (meet[m] == q + 1 and all(wpt.get(p, 0) == 1 for p in lines[m])) for m in Sv)
    dist_meet = {}
    for m in Sv:
        dist_meet[meet[m]] = dist_meet.get(meet[m], 0) + 1
    check("N2 each spread line != v meets q+1 W lines (one per point) or none", ok_meet,
          "histogram of #W lines met: %s" % dict(sorted(dist_meet.items())))
    none = sorted(m for m in Sv if meet[m] == 0)
    check("N3 exactly q^2 spread lines != v meet no W line", len(none) == q * q, "%d" % len(none))
    nu0 = sorted(m for m in Sv if nu_of[m] == 0)
    check("N4 these are exactly the spread lines != v with nu = 0", nu0 == none,
          "#nu=0: %d; distinct nu values: %s" % (len(nu0), sorted(set(nu_of.values()))))
    RL = sorted(set(Lv) | Wset | set(none))
    check("R0 L_v, W, S_0 disjoint and |R_L| = q^4+q^2+q", len(RL) == len(Lv) + len(W) + len(none) == q ** 4 + q * q + q,
          "|R_L| = %d (want %d)" % (len(RL), q ** 4 + q * q + q))
    RLs = set(RL)
    ptG = [[l for l in pt_lines[p] if l in RLs] for p in range(N)]
    off = None
    for l in RL:
        meet_pts = {p for p in lines[l] if any(m != l for m in ptG[p])}
        if len(meet_pts) > 1:
            off = l
            break
    check("R1 R_L is a dual segment set", off is None, "offending line: %s" % off)
    check("R2 every point of H(q) lies on a line of R_L", all(ptG[p] for p in range(N)))
    # maximality: G + m is a dual segment set iff (a) the G-lines meeting m all pass through one point of m and
    # (b) every G-line l meeting m at p has its G-neighbours (if any) through p
    sG = {}
    for l in RL:
        pm = {p for p in lines[l] if any(m != l for m in ptG[p])}
        sG[l] = next(iter(pm)) if pm else None
    addable = []
    for m in range(L):
        if m in RLs:
            continue
        A, viol = set(), False
        for p in lines[m]:
            gl = ptG[p]
            if gl:
                A.add(p)
                for l in gl:
                    if sG[l] is not None and sG[l] != p:
                        viol = True
        if len(A) >= 2:
            viol = True
        if not viol:
            addable.append(m)
    check("R3 maximal: no line outside R_L can be added", len(addable) == 0, "addable lines: %d" % len(addable))
    if q <= 4:
        brute = [m for m in range(L) if m not in RLs and dual_seg_ok(RL + [m])]
        check("R3b brute-force cross-check of R3 (full dual-segment test of R_L + m)", brute == addable,
              "brute addable: %d" % len(brute))
    PS = sorted({p for l in S_ids for p in lines[l]})
    check("P1 P_S has (q+1)(q^3+1) points", len(PS) == (q + 1) * (q ** 3 + 1), "%d" % len(PS))
    PSs = set(PS)
    seg = True
    for p in PS:
        if sum(1 for l in pt_lines[p] if any(x != p and x in PSs for x in lines[l])) > 1:
            seg = False
            break
    check("P2 P_S is a segment set", seg)

def dual_seg_ok(G):
    Gs = set(G)
    ptG = [[l for l in pt_lines[p] if l in Gs] for p in range(N)]
    for l in G:
        meet_pts = {p for p in lines[l] if any(m != l for m in ptG[p])}
        if len(meet_pts) > 1:
            return False
    return True

# ---------- run: first zero-free pair in full, the others summarised ----------
if not good:
    print("q=%d: no zero-free G; whisker sets do not exist here." % q)
    tot = sum(1 for r in results if r[1])
    print("RESULT q=%d src=%s: passed %d / %d checks" % (q, src, tot, len(results)))
    sys.exit(0)

summary = []
for k, (c0, c1) in enumerate(good):
    before = len(results)
    if k == 0:
        print("=== (c0,c1) = (%d,%d), delta = %d ===" % (c0, c1, DEL))
        run_pair(c0, c1)
        first_block = list(results[before:])
    else:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            run_pair(c0, c1)
        blk = results[before:]
        summary.append(((c0, c1), sum(1 for r in blk if r[1]), len(blk), [r[0][:3] for r in blk if not r[1]]))
    if k > 0:
        blk = results[before:]
        print("   (c0,c1)=(%d,%d): %d/%d pass%s" % (c0, c1, sum(1 for r in blk if r[1]), len(blk),
              "" if all(r[1] for r in blk) else "  FAILS " + str([r[0][:3] for r in blk if not r[1]])), flush=True)
        results[before:] = []   # keep the report to the first pair
if len(good) > 1:
    print("zero-free (c0,c1) pairs: %d; with every W/N/R/P check passing for each pair: %d" % (
        len(good), 1 + sum(1 for s in summary if s[3] == [])))
    print("pairs tested with W/N/R/P: %s" % [g for g in good])
tot = sum(1 for r in results if r[1])
print("RESULT q=%d src=%s: passed %d / %d checks (setup + first pair (c0,c1)=(%d,%d))" % (
    q, src, tot, len(results), good[0][0], good[0][1]))
