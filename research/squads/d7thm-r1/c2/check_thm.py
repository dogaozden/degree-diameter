#!/usr/bin/env python3
"""Card c2 of squad round d7thm-r1: independent numpy checks of the odd-q claims in BRIEF.md.
Usage: python3 check_thm.py q        (reads hex/hex_q{q}.bin written by hexgen2)"""
import sys, json
import numpy as np

q = int(sys.argv[1])
BIN = f"hex/hex_q{q}.bin"
checks = []


def check(name, ok, detail=""):
    ok = bool(ok)
    checks.append({"name": name, "passed": ok, "detail": str(detail)})
    print(("PASS " if ok else "FAIL ") + name + (("  [" + str(detail) + "]") if str(detail) != "" else ""), flush=True)


# ---------------- field GF(q), own implementation ----------------
# q = 9: element e = a0 + 3*a1 means a0 + a1*x with x^2 = -1 over GF(3).  q = 11: prime field.
def e_add(a, b):
    if q == 9:
        return (a % 3 + b % 3) % 3 + 3 * ((a // 3 + b // 3) % 3)
    return (a + b) % 11


def e_mul(a, b):
    if q == 9:
        a0, a1, b0, b1 = a % 3, a // 3, b % 3, b // 3
        return (a0 * b0 - a1 * b1) % 3 + 3 * ((a0 * b1 + a1 * b0) % 3)
    return (a * b) % 11


ADD = np.array([[e_add(a, b) for b in range(q)] for a in range(q)], dtype=np.int64)
MUL = np.array([[e_mul(a, b) for b in range(q)] for a in range(q)], dtype=np.int64)
NEG = np.array([int(np.where(ADD[a] == 0)[0][0]) for a in range(q)], dtype=np.int64)
INV = np.array([-1] + [int(np.where(MUL[a] == 1)[0][0]) for a in range(1, q)], dtype=np.int64)
SUB = ADD[np.arange(q)[:, None], NEG[None, :]]  # SUB[a,b] = a - b
A3 = np.arange(q)
ok_field = (np.all(MUL[MUL[:, :, None], A3[None, None, :]] == MUL[A3[:, None, None], MUL[None, :, :]])
            and np.all(MUL[A3[:, None, None], ADD[None, :, :]] == ADD[MUL[:, :, None], MUL[:, None, :]])
            and np.all(ADD[ADD[:, :, None], A3[None, None, :]] == ADD[A3[:, None, None], ADD[None, :, :]])
            and np.all(MUL == MUL.T) and np.all(ADD == ADD.T) and np.all(INV[1:] >= 0)
            and np.all(MUL[np.arange(1, q), INV[1:]] == 1))
check(f"GF({q}) own tables form a field (assoc/distrib/inverses)", ok_field)
SQ = set(int(MUL[x, x]) for x in range(1, q))
NONSQ = [x for x in range(1, q) if x not in SQ]

# ---------------- load H(q) ----------------
hdr = np.fromfile(BIN, dtype=np.int32, count=3)
qq, N, L = int(hdr[0]), int(hdr[1]), int(hdr[2])
N_exp = (q ** 6 - 1) // (q - 1)
check("header: q, N=L=(q^6-1)/(q-1)", qq == q and N == N_exp and L == N_exp, f"N={N} L={L} expect {N_exp}")
LP = np.fromfile(BIN, dtype=np.int32, count=L * (q + 1), offset=12).reshape(L, q + 1).astype(np.int64)
X = np.fromfile(BIN, dtype=np.uint8, count=N * 7, offset=12 + 4 * L * (q + 1)).reshape(N, 7).astype(np.int64)
X0, X1, X2, X3, X4, X5, X6 = [X[:, i] for i in range(7)]

ar = np.arange(N)
lead = np.argmax(X != 0, axis=1)
check("points normalized (first nonzero coord = 1) and pairwise distinct",
      np.all(X[ar, lead] == 1) and len(np.unique(X @ (q ** np.arange(7)))) == N)

Qv = SUB[ADD[ADD[MUL[X0, X4], MUL[X1, X5]], MUL[X2, X6]], MUL[X3, X3]]
check("every stored point satisfies Q(X)=X0X4+X1X5+X2X6-X3^2=0 (own GF arithmetic)",
      np.all(Qv == 0), f"nonzero Q values: {int((Qv != 0).sum())}")

PL_cnt = np.bincount(LP.ravel(), minlength=N)
check("every point on q+1 lines; every line has q+1 distinct points",
      np.all(PL_cnt == q + 1) and all(len(set(r)) == q + 1 for r in LP[:: max(1, L // 2000)]))

# Tits equations on Pluecker coordinates of the first two points of each line
P = X[LP[:, 0]]
R = X[LP[:, 1]]


def pl(i, j):
    return SUB[MUL[P[:, i], R[:, j]], MUL[P[:, j], R[:, i]]]


tits = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
tits_ok = np.ones(L, dtype=bool)
for (a, b), (c, d) in tits:
    tits_ok &= (pl(a, b) == pl(c, d))
check("every line satisfies the six Tits equations on Pluecker coordinates", np.all(tits_ok),
      f"failing lines: {int((~tits_ok).sum())}")


def normalize(W):
    idx = np.argmax(W != 0, axis=1)
    ld = W[np.arange(len(W)), idx]
    assert np.all(ld != 0)
    return MUL[INV[ld][:, None], W]


pcodes = X @ (q ** np.arange(7))
order = np.argsort(pcodes)
scodes = pcodes[order]


def lookup(W):
    c = normalize(W) @ (q ** np.arange(7))
    pos = np.searchsorted(scodes, c)
    pos = np.minimum(pos, N - 1)
    assert np.all(scodes[pos] == c), "span point not stored"
    return order[pos]


span_ids = np.stack([lookup(ADD[P, MUL[lam, R]]) for lam in range(q)] + [lookup(R)], axis=1)
check("every line = normalized span of its first two points (q+1 points, same set)",
      np.all(np.sort(span_ids, axis=1) == np.sort(LP, axis=1)))
check("lines pairwise distinct", len(np.unique(np.sort(LP, axis=1), axis=0)) == L)

# incidence: point -> lines
flat = LP.ravel()
PL = (np.argsort(flat, kind="stable") // (q + 1)).reshape(N, q + 1)

# BFS in incidence graph from a line
def bfs(src):
    dL = np.full(L, -1)
    dP = np.full(N, -1)
    dL[src] = 0
    front = np.array([src])
    d = 0
    while front.size:
        pts = np.unique(LP[front].ravel())
        pts = pts[dP[pts] < 0]
        dP[pts] = d + 1
        lines = np.unique(PL[pts].ravel())
        lines = lines[dL[lines] < 0]
        dL[lines] = d + 2
        front = lines
        d += 2
    return dL, dP


e1 = np.array([0, 1, 0, 0, 0, 0, 0]); e6 = np.array([0, 0, 0, 0, 0, 0, 1])
p_e1 = int(np.where((X == e1).all(1))[0][0]); p_e6 = int(np.where((X == e6).all(1))[0][0])
cand = set(PL[p_e1].tolist()) & set(PL[p_e6].tolist())
assert len(cand) == 1
v = cand.pop()
dL, dP = bfs(v)
check("H(q) connected, eccentricity of v is 6 (lines) / 5 (points)",
      dL.min() >= 0 and dP.min() >= 0 and dL.max() == 6 and dP.max() == 5,
      f"max line dist {dL.max()}, max point dist {dP.max()}")

# ---------------- Pi, S, P_S ----------------
sq_nonsq = NONSQ
c = None
C_CHOICES = [cc for cc in range(1, q) if int(NEG[cc]) in NONSQ]  # -c non-square
c = C_CHOICES[0] if len(sys.argv) < 3 else int(sys.argv[2])
import os
assert c in C_CHOICES or os.environ.get("NEG_CTRL"), "c must have -c a non-square"
f0 = ADD[X0, MUL[c, X4]]                  # X0 + c X4
inPi = (f0 == 0)
LPPi = inPi[LP]
inS = LPPi.all(1)
check("Pi: X0+cX4=0 with -c a non-square (c chosen)", int(NEG[c]) in NONSQ, f"c={c}, -c={int(NEG[c])}, valid c: {C_CHOICES}")
check("|P_S| = (q+1)(q^3+1) (points of H(q) in Pi)", inPi.sum() == (q + 1) * (q ** 3 + 1), int(inPi.sum()))
check("|S| = q^3+1 lines of H(q) inside Pi", inS.sum() == q ** 3 + 1, int(inS.sum()))
sid = -np.ones(N, dtype=np.int64)
Sl = np.where(inS)[0]
for s in Sl:
    sid[LP[s]] = s
# each Pi point on exactly one S line
cnt_S_through = inS[PL].sum(1)
check("S is a spread of P_S: every point of P_S on exactly one S-line", np.all(cnt_S_through[inPi] == 1)
      and np.all(cnt_S_through[~inPi] == 0))
# no line of H(q) meets two S-lines (for lines m, distinct S-lines among its points, excluding m itself)
sidL = np.where(LPPi, sid[LP], -1)
srt = np.sort(sidL, axis=1)
distinct = (srt[:, 0] >= 0).astype(int) + ((srt[:, 1:] != srt[:, :-1]) & (srt[:, 1:] >= 0)).sum(1)
selfS = inS.astype(int)
meets_other = distinct - selfS
check("pairwise opposite: no line of H(q) meets two lines of S",
      np.all(meets_other <= 1), f"max S-lines met by one line: {int(meets_other.max())}")

# ---------------- v, L_v, distance <= 3, free points ----------------
check("v (through e1,e6) exists and lies in S", inS[v], f"v={v}")
Lv_mask = np.zeros(L, dtype=bool)
Lv_mask[PL[LP[v]].ravel()] = True
Lv_mask[v] = False
check("|L_v| = q(q+1) lines != v meeting v", Lv_mask.sum() == q * (q + 1), int(Lv_mask.sum()))
D3 = np.zeros(N, dtype=bool)
D3[LP[v]] = True
D3[LP[Lv_mask]] = True
check("points at distance <= 3 from v are exactly X2=X5=0 (and there are (q+1)(q^2+1))",
      np.array_equal(D3, (X2 == 0) & (X5 == 0)) and D3.sum() == (q + 1) * (q * q + 1),
      int(D3.sum()))
free = (~inPi) & (~D3)
bfs_free = (dP == 5) & (~inPi)
check("free points = not in Pi and at distance 5 from v; count q^3(q^2-1)",
      np.array_equal(free, bfs_free) and free.sum() == q ** 3 * (q * q - 1), int(free.sum()))

# ---------------- G, nu, F, W ----------------
G_ok_pairs = []
c0 = c1 = None
AB = np.array([(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)])
for x0 in range(q):
    for x1 in range(q):
        a, b = AB[:, 0], AB[:, 1]
        t1 = ADD[MUL[x0, a], MUL[x1, b]]
        t2 = ADD[MUL[a, a], MUL[c, MUL[b, b]]]
        Gv = SUB[MUL[t1, t2], MUL[b, MUL[b, b]]]
        if np.all(Gv != 0):
            G_ok_pairs.append((x0, x1))
if G_ok_pairs:
    c0, c1 = G_ok_pairs[0]
check("G(a,b)=(c0a+c1b)(a^2+cb^2)-b^3 zero-free on F^2\\0 for some (c0,c1)", c0 is not None,
      f"(c0,c1)=({c0},{c1}); {len(G_ok_pairs)} valid pairs of {q*q}")


def G(a, b):
    t1 = ADD[MUL[c0, a], MUL[c1, b]]
    t2 = ADD[MUL[a, a], MUL[c, MUL[b, b]]]
    return int(SUB[MUL[t1, t2], MUL[b, MUL[b, b]]])


den_nu = ADD[MUL[c, MUL[X2, X2]], MUL[X5, X5]]
num_nu = SUB[MUL[X2, X3], MUL[X4, X5]]
nu = np.where(den_nu == 0, -1, MUL[num_nu, INV[np.where(den_nu == 0, 1, den_nu)]])

W_lines, W_pi, W_z = [], [], []
per_z_counts = {}
n_onv = 0
for a in range(q):
    for b in range(q):
        if a == 0 and b == 0:
            continue
        g = ADD[f0[LP], ADD[MUL[a, X2[LP]], MUL[b, X5[LP]]]]
        inSz = (g == 0).all(1)
        cl = np.where(inSz & (~inS))[0]
        per_z_counts[(a, b)] = int(cl.size)
        if cl.size == 0:
            continue
        pm = (f0[LP[cl]] == 0)
        assert np.all(pm.sum(1) == 1), "line in Pi_z not in S must meet Pi in one point"
        xs = LP[cl][pm]
        onv = den_nu[xs] == 0
        n_onv += int(onv.sum())
        Fz = int(MUL[G(a, b), INV[ADD[MUL[a, a], MUL[c, MUL[b, b]]]]])
        ok = (~onv) & (nu[xs] == Fz)
        W_lines.append(cl[ok]); W_pi.append(xs[ok]); W_z.append(np.tile([a, b], (int(ok.sum()), 1)))
W_lines = np.concatenate(W_lines); W_pi = np.concatenate(W_pi); W_z = np.concatenate(W_z)
print(f"  diag: candidate lines (S_z not in S) over all z: {sum(per_z_counts.values())}; "
      f"Pi-point on v (nu undefined, excluded): {n_onv}")
uniq_W = np.unique(W_lines)
check("W lines are distinct over different z (no line counted twice)", len(uniq_W) == len(W_lines),
      f"{len(W_lines)} incidences, {len(uniq_W)} distinct")
W = uniq_W
Wpi_of = np.zeros(L, dtype=np.int64); Wpi_of[W_lines] = W_pi
check("|W| = q^2(q^2-1)", len(W) == q * q * (q * q - 1), len(W))
check("W lines are not in S", not inS[W].any())
check("no point of a W line at distance <= 3 from v", not D3[LP[W]].any())
cntW = np.bincount(LP[W].ravel(), minlength=N)
check("each free point lies on exactly one W line", np.all(cntW[free] == 1),
      f"free-point W-degree histogram: {np.bincount(cntW[free]).tolist()}")
check("each W line meets Pi in one point which is off v (nu defined)", np.all(~D3[W_pi]) and len(W_pi) == len(W_lines))

# ---------------- claim 3: nu on spread lines, incidence with W ----------------
Sidx = np.array([s for s in Sl if s != v])
nuL = nu[LP[Sidx]]
check("nu constant on each spread line != v (and well defined there)",
      np.all(nuL == nuL[:, :1]) and np.all(nuL >= 0), f"lines with non-constant nu: {int((nuL != nuL[:, :1]).any(1).sum())}")
nu_s = nuL[:, 0]
wpt = np.bincount(W_pi, minlength=N)
wc = wpt[LP[Sidx]].sum(1)
check("each spread line != v meets q+1 or 0 W-lines (one per point)",
      np.all((wc == 0) | (wc == q + 1)) and np.all(wpt[LP[Sidx[wc == q + 1]]] == 1),
      f"counts histogram: {dict((int(k), int(v)) for k, v in zip(*np.unique(wc, return_counts=True)))}")
check("sum over spread lines of W-incidences = |W| (each W line meets one spread line)", int(wc.sum()) == len(W))
zero_sl = Sidx[wc == 0]
check("exactly q^2 spread lines != v meet no W-line", len(zero_sl) == q * q, len(zero_sl))
check("the spread lines meeting no W-line are exactly those with nu = 0",
      set(zero_sl.tolist()) == set(Sidx[nu_s == 0].tolist()), f"#nu=0 lines: {int((nu_s == 0).sum())}")

# ---------------- claim 4: R_L dual segment set ----------------
S0 = zero_sl
Rl_parts = [np.where(Lv_mask)[0], W, S0]
R = np.concatenate(Rl_parts)
inR = np.zeros(L, dtype=bool); inR[R] = True
check("R_L = L_v + W + S_0 has q^4+q^2+q lines (disjoint parts)",
      len(R) == q ** 4 + q * q + q and inR.sum() == len(R), f"|R_L|={len(R)} expect {q**4+q*q+q}")
cntR = np.bincount(LP[R].ravel(), minlength=N)
check("every point of H(q) lies on a line of R_L", np.all(cntR >= 1), f"uncovered points: {int((cntR == 0).sum())}")
TsR = np.zeros(L, dtype=np.int64)
TsR = ((cntR[LP] >= 2).sum(1))
check("R_L is a dual segment set: each line of R_L has at most one point shared with other R_L lines",
      np.all(TsR[R] <= 1), f"max: {int(TsR[R].max())}, lines with 2+: {int((TsR[R] >= 2).sum())}")
# maximality: adding any outside line m must break the dual segment property
lineR = np.full(N, -1, dtype=np.int64)
pts1 = np.where(cntR == 1)[0]
lr = PL[pts1]
lineR[pts1] = lr[np.arange(len(pts1)), np.argmax(inR[lr], axis=1)]
badpt = np.zeros(N, dtype=bool)
badpt[pts1] = TsR[lineR[pts1]] >= 1
out = np.where(~inR)[0]
cov_m = (cntR[LP[out]] >= 1).sum(1)
viol = (cov_m >= 2) | badpt[LP[out]].any(1)
check("maximal: no line outside R_L can be added (every outside line violates)", np.all(viol),
      f"addable outside lines: {int((~viol).sum())} of {len(out)}")

# ---------------- claim 5: P_S segment set ----------------
fcnt_line = LPPi.sum(1)
multi = (fcnt_line[PL] >= 2).sum(1)
PSpts = np.where(inPi)[0]
check("P_S is a segment set: for each p, at most one line through p contains other P_S points",
      np.all(multi[PSpts] <= 1), f"max lines-with-other-points through a P_S point: {int(multi[PSpts].max())}")
check("|P_S| = (q+1)(q^3+1) and it is a segment set of that size", len(PSpts) == (q + 1) * (q ** 3 + 1))

npass = sum(ch["passed"] for ch in checks)
print(f"\nq={q}: checks passed {npass} of {len(checks)}")
with open(f"results_q{q}_c{c}.json", "w") as fh:
    json.dump({"q": q, "c": int(c), "valid_c": [int(x) for x in C_CHOICES], "c0c1": [int(c0), int(c1)], "passed": npass, "total": len(checks),
               "checks": checks, "v": int(v), "W": int(len(W)), "R_L": int(len(R)), "S0": int(len(S0))}, fh, indent=1)
