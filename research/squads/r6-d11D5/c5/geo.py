#!/usr/bin/env python3
"""Card c5, squad r6-d11D5: geometry of a K33 start (n = 588) that satisfies as many coset-0 demands as possible.

Same construction as research/d11D5/dc/kkk.py with K = 3 and complete incidence: new points X_0..X_2 (ids 585..587)
and new lines l_0..l_2 (ids 585..587), every X_j on every l_g.  Hyperbolic line h_j (9 points) gives
  Ra_j     spare point: sigma(X_j) = delta(Ra_j), sigma(C^-1(Ra_j)) = one new line (pairing perm, searched);
  keep_j   6 points R: the old line delta(R) (a switch line) gets X_j in place of a removed point p;
  omitted  the other 2 points of h_j (their lines are not switched).
Each removed p goes to one new line l_g; each l_g takes 6 removed points, pairwise non-collinear (as in kkk.py).
Switch lines of different h_j are distinct; hyperbolic lines may share one point (two lines share <= 1 point), but a
point used as a switch line is never shared, and a spare point is never a switch line.

Demands (8 pairs each, per switch = (switch line L = delta(R), removed point p on L)):
  (i)  pairs (p, z), z on L, z != p: satisfied iff C(L) is totally isotropic, i.e. R in S;
  (ii) pairs (L, m), m an old line through p, m != L: satisfied iff C^-1(delta(p)) is totally isotropic, i.e. p in T.
S = {R : C(delta(R)) isotropic}, T = {p : C^-1(delta(p)) isotropic}.  Maximum 8 * (18 + 18) = 288.

The search (simulated annealing) maximises 8 * (#switch lines in S + #removed points in T) minus a penalty per
violated structural condition.  The best states are then written in plusopt format, the spare/pairing choices (which do
not enter the demands) are swept with po7, and the best start is written to OUT.

usage: python3 geo.py CSEED OUT.in [RESTARTS=3] [ITERS=80000]
  C = random non-symplectic collineation from CSEED.  Writes OUT.in (plusopt format) and OUT.in.json (the state).
"""
import sys, os, random, math, subprocess, json, itertools

sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *   # n0, LINES, d_pt, PTS, Bf, span, is_W, pmap, matinv, randmat

K = 3
NEW = [n0 + j for j in range(K)]     # ids of the new points (and of the new lines, same numbering)
WPEN = 16                            # penalty per violated structural condition (one demand is worth 8)
PO7 = "/tmp/po7"

col = [set() for _ in range(n0)]     # col[a] = points collinear with a (including a)
for _l in LINES:
    for _a in _l:
        col[_a].update(_l)


def po7_cost(path):
    out = subprocess.run([PO7, path], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
    return int(out.split("cost=")[1].split()[0])


def hyperbolic_lines():
    """All 4160 hyperbolic lines of PG(3,8) (9 points, pairwise non-orthogonal), as sorted point lists."""
    done, H = set(), []
    for a in range(n0):
        for b in range(a + 1, n0):
            if a * n0 + b in done or not Bf(PTS[a], PTS[b]):
                continue
            h = sorted(span(PTS[a], PTS[b]))
            H.append(h)
            for x in h:
                for y in h:
                    if x < y:
                        done.add(x * n0 + y)
    return H


def make_C(rng):
    while True:   # non-symplectic: some W-line is not mapped to a W-line
        M = randmat(rng); C = pmap(M)
        if sum(is_W([C[p] for p in l[:2]]) for l in LINES) < n0:
            break
    Cinv = pmap(matinv(M))
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    T = set(p for p in range(n0) if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]]))
    return C, Cinv, S, T


# state: hid[3] (index into H), ra[3] (spare points), sw[3] = 6 records [R, p, g] per hyperbolic line
#   R = switch point (old line delta(R) receives X_j), p = removed point on delta(R), g = new line of p (0..2)
def keeps(st, j):
    return [r[0] for r in st['sw'][j]]


def copy_state(st):
    return {'hid': st['hid'][:], 'ra': st['ra'][:], 'sw': [[r[:] for r in s] for s in st['sw']]}


def objective(st, S, T):
    recs = [r for j in range(K) for r in st['sw'][j]]
    Rs = [r[0] for r in recs]; Ps = [r[1] for r in recs]
    A = sum(1 for R in Rs if R in S)
    B = sum(1 for p in Ps if p in T)
    pen = (len(Rs) - len(set(Rs))) + (len(Ps) - len(set(Ps)))     # a point switched twice / removed twice
    ks = set(Rs)
    pen += sum(1 for r in st['ra'] if r in ks) + (K - len(set(st['ra'])))   # spare is never a switch line
    for g in range(K):                                              # each new line: pairwise non-collinear points
        mem = [r[1] for r in recs if r[2] == g]
        for a in range(len(mem)):
            for b in range(a + 1, len(mem)):
                if mem[b] in col[mem[a]]:
                    pen += 1
    return 8 * (A + B) - WPEN * pen, A, B, pen


def setup(st, j, newid, labels, H, S, rng):
    """Install hyperbolic line H[newid] as h_j: spare = a non-S point, keep = 6 points with S-points first (kkk.py)."""
    h = H[newid]
    st['hid'][j] = newid
    ra = sorted(h, key=lambda R: (R in S, rng.random()))[0]
    keep = [R for R in sorted(h, key=lambda R: (R not in S, rng.random())) if R != ra][:6]
    st['ra'][j] = ra
    st['sw'][j] = [[R, rng.choice(LINES[d_pt[R]]), labels[k]] for k, R in enumerate(keep)]


def init_state(rng, H, S, Hgood):
    st = {'hid': [0] * K, 'ra': [0] * K, 'sw': [None] * K}
    labels = [0] * 6 + [1] * 6 + [2] * 6
    rng.shuffle(labels)
    hids = rng.sample(Hgood, K)
    for j in range(K):
        setup(st, j, hids[j], labels[6 * j: 6 * j + 6], H, S, rng)
    return st


def move(st, rng, H, S, Hgood):
    u = rng.random(); j = rng.randrange(K)
    h = H[st['hid'][j]]
    kp = keeps(st, j)
    if u < 0.25:       # switch a kept point with an omitted point of the same hyperbolic line
        om = [x for x in h if x != st['ra'][j] and x not in kp]
        rec = st['sw'][j][rng.randrange(6)]
        x = rng.choice(om); rec[0] = x; rec[1] = rng.choice(LINES[d_pt[x]])
    elif u < 0.40:     # change the spare point (the old spare becomes omitted)
        om = [x for x in h if x != st['ra'][j] and x not in kp]
        st['ra'][j] = rng.choice(om)
    elif u < 0.70:     # change the removed point on a switch line
        rec = st['sw'][j][rng.randrange(6)]
        rec[1] = rng.choice(LINES[d_pt[rec[0]]])
    elif u < 0.90:     # exchange the new lines of two removed points (group sizes stay 6)
        j2 = rng.randrange(K)
        r1 = st['sw'][j][rng.randrange(6)]; r2 = st['sw'][j2][rng.randrange(6)]
        r1[2], r2[2] = r2[2], r1[2]
    else:              # replace hyperbolic line h_j (keeps the multiset of its six group labels)
        newid = rng.choice(Hgood) if rng.random() < 0.5 else rng.randrange(len(H))
        labels = [r[2] for r in st['sw'][j]]; rng.shuffle(labels)
        setup(st, j, newid, labels, H, S, rng)


def anneal(rng, H, S, T, Hgood, iters, t0=3.0, t1=0.05):
    st = init_state(rng, H, S, Hgood)
    f = objective(st, S, T)[0]
    best = None
    for it in range(iters):
        temp = t0 * (t1 / t0) ** (it / iters)
        new = copy_state(st); move(new, rng, H, S, Hgood)
        f2, A2, B2, pen2 = objective(new, S, T)
        if f2 >= f or rng.random() < math.exp((f2 - f) / temp):
            st, f = new, f2
            if pen2 == 0 and (best is None or f > best[0]):
                best = (f, copy_state(st))
    return best


def write_start(st, C, Cinv, perm, path):
    """plusopt file: sigma = delta o C on old points, except sigma(C^-1(Ra_j)) = new line perm[j] and sigma(X_j) = delta(Ra_j)."""
    L2 = [list(l) for l in LINES]
    groups = [[] for _ in range(K)]
    for j in range(K):
        for R, p, g in st['sw'][j]:
            L = d_pt[R]
            L2[L] = [NEW[j] if q == p else q for q in L2[L]]
            groups[g].append(p)
    for g in range(K):
        L2.append(groups[g] + NEW)
    sig = [d_pt[C[p]] for p in range(n0)]
    for j in range(K):
        sig[Cinv[st['ra'][j]]] = n0 + perm[j]
    sig += [d_pt[st['ra'][j]] for j in range(K)]
    n = n0 + K
    ok = sorted(sig) == list(range(n)) and all(len(l) == 9 for l in L2)
    with open(path, 'w') as f:
        f.write(f"{n} 9\n")
        for l in L2:
            f.write(" ".join(map(str, l)) + "\n")
        for s in sig:
            f.write(f"{s}\n")
    return ok


def sweep_variants(st, H, C, Cinv, tmp):
    """Spare points (any non-switch point of each h_j) and the pairing of spares with new lines: po7 picks the best."""
    kps = [set(keeps(st, j)) for j in range(K)]
    allk = set().union(*kps)
    opts = [[x for x in H[st['hid'][j]] if x not in kps[j]] for j in range(K)]
    best = None
    for ra in itertools.product(*opts):
        if len(set(ra)) < K or any(x in allk for x in ra):
            continue
        for perm in itertools.permutations(range(K)):
            s2 = copy_state(st); s2['ra'] = list(ra)
            if not write_start(s2, C, Cinv, perm, tmp):
                continue
            c = po7_cost(tmp)
            if best is None or c < best[0]:
                best = (c, list(ra), perm)
    if os.path.exists(tmp):
        os.remove(tmp)
    return best


if __name__ == "__main__":
    cseed = int(sys.argv[1]); out = sys.argv[2]
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 80000
    rng = random.Random(cseed)
    H = hyperbolic_lines()
    if os.environ.get('PARA') == '1':   # parabolic C (k22p.parabolic_C): |S| = 73, whole hyperbolic lines inside S
        import k22p
        M, C, Sl = k22p.parabolic_C(rng); Cinv = pmap(matinv(M)); S = set(Sl)
        T = set(p for p in range(n0) if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]]))
    else:
        C, Cinv, S, T = make_C(rng)
    Hgood = sorted(range(len(H)), key=lambda i: -len(S & set(H[i])))[:400]
    print(f"C seed {cseed}: |S| = {len(S)}, |T| = {len(T)}, best |S cap h| = {len(S & set(H[Hgood[0]]))}, "
          f"hyperbolic lines {len(H)}", flush=True)
    tmp = out + ".tmp.in"
    results = []
    for r in range(restarts):
        best = anneal(rng, H, S, T, Hgood, iters)
        if best is None:
            print(f"restart {r}: no feasible state", flush=True); continue
        f, st = best
        _, A, B, pen = objective(st, S, T)
        v = sweep_variants(st, H, C, Cinv, tmp)
        c, ra, perm = v
        print(f"restart {r}: switch lines in S = {A}/18, removed in T = {B}/18, demands = {8 * (A + B)}/288, "
              f"pen = {pen}; po7 start cost {c} (ra {ra}, perm {perm})", flush=True)
        results.append((c, 8 * (A + B), r, st, ra, perm))
    if not results:
        sys.exit(1)
    c, dem, r, st, ra, perm = min(results, key=lambda x: x[0])
    st = copy_state(st); st['ra'] = list(ra)
    write_start(st, C, Cinv, perm, out)
    with open(out + ".json", "w") as f:
        json.dump({'cseed': cseed, 'demands': dem, 'po7_start': c, 'hyp_lines': [H[i] for i in st['hid']],
                   'ra': st['ra'], 'sw': st['sw'], 'perm': list(perm)}, f)
    print(f"best: start cost {c}, demands {dem}/288, restart {r}, file {out}", flush=True)
