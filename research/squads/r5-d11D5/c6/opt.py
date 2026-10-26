"""Card c6: optimise the free choices of the two-switch construction (mkdc2.py KS=2) for the lowest start cost.

Free choices (state st):
  h[k]   hyperbolic PG-line (9 point ids, sorted) of switch k (k = 0, 1); the switch lines are delta(h[k][i]), i != om[k]
  om[k]  index of the omitted point of h[k]
  ps[k]  the 8 points p_i (p_i on switch line i, pairwise non-collinear, not shared between switches)
  R9[k]  sigma(x*_k) = delta(R9[k]); the old point Cinv(R9[k]) takes sigma = l*_k  (mkdc2: R9 = h[om])
  M      C = pmap(M), a collineation of PG(3,8); symplectic left moves T*M keep C(L) isotropic for all W-lines L
Each candidate is built in memory, written to a scratch file and scored by SCORE=1 /tmp/po7 (structural cost).

usage: opt.py SECS SEED OUTDIR [INIT_TRIES]
"""
import sys, os, json, random, subprocess, time, math
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *

SECS = float(sys.argv[1]); SEED = int(sys.argv[2]); OUTDIR = sys.argv[3]
INIT_TRIES = int(sys.argv[4]) if len(sys.argv) > 4 else 12
T0 = float(os.environ.get("OPT_T0", "12")); T1 = float(os.environ.get("OPT_T1", "0.5"))
KS = 2
SCRATCH = os.environ.get("SCRATCH", "/tmp/claude-0/-home-user-degree-diameter/468680c1-3e6e-599d-b1ca-881241eddc40/scratchpad/c6")
os.makedirs(SCRATCH, exist_ok=True); os.makedirs(OUTDIR, exist_ok=True)
CAND = os.path.join(SCRATCH, "cand.in")
rng = random.Random(SEED)
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
ENV = dict(os.environ); ENV["SCORE"] = "1"; ENV["THREADS"] = "1"
NSCORE = [0]


def score_file(fn):
    NSCORE[0] += 1
    o = subprocess.run(["/tmp/po7", fn], env=ENV, capture_output=True, text=True).stdout
    return int(o.split("cost=")[1].split()[0])


def rand_h(pool=None):
    while True:
        a, b = rng.sample(pool if pool else range(n0), 2)
        if Bf(PTS[a], PTS[b]): return tuple(sorted(span(PTS[a], PTS[b])))


_cache = {}
def CC(M):
    key = tuple(tuple(r) for r in M)
    if key not in _cache:
        if len(_cache) > 3000: _cache.clear()
        _cache[key] = (pmap(M), pmap(matinv(M)))
    return _cache[key]


def build(st):
    """Return (n, L2, sig) or None when the choices are inconsistent."""
    C, Cinv = CC(st["M"])
    usedL = set(); usedP = set(); sw = []
    for k in range(KS):
        h = st["h"][k]; om = st["om"][k]; ps = st["ps"][k]
        Ls = [d_pt[h[i]] for i in range(9) if i != om]
        if any(L in usedL for L in Ls) or len(ps) != 8: return None
        for i, (L, p) in enumerate(zip(Ls, ps)):
            if p not in LSET[L] or p in usedP or any(p in col[q] for q in ps[:i]): return None
        sw.append((Ls, ps, st["R9"][k])); usedL.update(Ls); usedP.update(ps)
    n = n0 + KS
    L2 = [list(l) for l in LINES]
    sig = [d_pt[C[p]] for p in range(n0)]
    for k, (Ls, ps, R9) in enumerate(sw):
        X = n0 + k
        for L, p in zip(Ls, ps): L2[L] = [X if q == p else q for q in L2[L]]
        L2.append(list(ps) + [X])
        s9 = Cinv[R9]
        if sig[s9] != d_pt[R9]: return None          # old preimage already taken by an earlier switch
        sig[s9] = n0 + k; sig.append(d_pt[R9])
    return n, L2, sig


def validate(b):
    n, L2, sig = b
    deg = [0] * n
    for l in L2:
        assert len(set(l)) == 9
        for p in l: deg[p] += 1
    assert all(d == 9 for d in deg), "degree"
    assert sorted(sig) == list(range(n)), "sigma not bijective"


def write_file(b, fn):
    n, L2, sig = b
    with open(fn, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")


def cost_of(st):
    b = build(st)
    if b is None: return None
    write_file(b, CAND)
    return score_file(CAND)


def cp(st):
    return {"h": [tuple(h) for h in st["h"]], "om": list(st["om"]), "R9": list(st["R9"]),
            "ps": [list(p) for p in st["ps"]], "M": [list(r) for r in st["M"]]}


def greedy_switch(h, usedL, usedP, Cinv):
    """mkdc2 build(): random omitted point, then random valid p_i (preferring C^-1(delta(p)) isotropic)."""
    perm = list(range(9)); rng.shuffle(perm)
    for om in perm:
        Ls = [d_pt[h[i]] for i in range(9) if i != om]
        if any(L in usedL for L in Ls): continue
        ps = []
        for L in Ls:
            good = [p for p in LINES[L] if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]]) and p not in usedP and all(p not in col[q] for q in ps)]
            if not good: good = [p for p in LINES[L] if p not in usedP and all(p not in col[q] for q in ps)]
            if not good: break
            ps.append(rng.choice(good))
        if len(ps) == 8: return om, ps
    return None


def init_state():
    h1 = rand_h(); Ls1 = [d_pt[R] for R in h1]
    while True:                                   # mkdc2: C(L_1..L_3) isotropic, not symplectic, nonempty axis
        M = randmat(rng)
        if not all(Bf(matvec(M, PTS[LINES[L][0]]), matvec(M, PTS[LINES[L][1]])) == 0 for L in Ls1[:3]): continue
        C = pmap(M)
        pres = [li for li, l in enumerate(LINES) if is_W([C[p] for p in l[:2]])]
        if len(pres) >= n0: continue
        axis = [li for li in range(n0) if all(set(LINES[li]) & set(LINES[m]) or li == m for m in pres)]
        if axis: break
    Cinv = pmap(matinv(M)); P0 = d_ln[axis[0]]
    plane = [p for p in range(n0) if Bf(PTS[p], PTS[P0]) == 0 and p != P0]
    r1 = greedy_switch(h1, set(), set(), Cinv)
    if r1 is None: return None
    om1, ps1 = r1
    usedL = {d_pt[h1[i]] for i in range(9) if i != om1}; usedP = set(ps1)
    for t in range(3000):
        h2 = rand_h(plane)
        if sum(d_pt[R] in usedL for R in h2) > 1: continue
        r2 = greedy_switch(h2, usedL, usedP, Cinv)
        if r2: break
    else:
        return None
    om2, ps2 = r2
    return {"h": [h1, h2], "om": [om1, om2], "R9": [h1[om1], h2[om2]], "ps": [ps1, ps2], "M": M}


def other_sets(st, k):
    """lines and points used by the other switches (KS = 2)."""
    usedL = set(); usedP = set()
    for j in range(KS):
        if j == k: continue
        h = st["h"][j]; om = st["om"][j]
        usedL.update(d_pt[h[i]] for i in range(9) if i != om); usedP.update(st["ps"][j])
    return usedL, usedP


def move_p(st):
    k = rng.randrange(KS); i = rng.randrange(8)
    h = st["h"][k]; om = st["om"][k]; ps = st["ps"][k]
    L = [d_pt[h[j]] for j in range(9) if j != om][i]
    _, usedP = other_sets(st, k)
    cands = [p for p in LINES[L] if p not in usedP and p != ps[i]
             and all(p not in col[q] for j, q in enumerate(ps) if j != i)]
    if not cands: return None
    s2 = cp(st); s2["ps"][k][i] = rng.choice(cands); return s2


def move_om(st):
    k = rng.randrange(KS); h = st["h"][k]
    om2 = rng.choice([o for o in range(9) if o != st["om"][k]])
    Ls = [d_pt[h[j]] for j in range(9) if j != om2]
    _, usedP = other_sets(st, k)
    ps = []
    for L in Ls:
        cands = [p for p in LINES[L] if p not in usedP and all(p not in col[q] for q in ps)]
        if not cands: return None
        ps.append(rng.choice(cands))
    s2 = cp(st); s2["om"][k] = om2; s2["ps"][k] = ps; return s2


def move_R9(st):
    k = rng.randrange(KS); s2 = cp(st); s2["R9"][k] = rng.randrange(n0); return s2


def matmul(A, B):
    return [[mul[A[i][0]][B[0][j]] ^ mul[A[i][1]][B[1][j]] ^ mul[A[i][2]][B[2][j]] ^ mul[A[i][3]][B[3][j]]
             for j in range(4)] for i in range(4)]


def transvection(symp):
    while True:
        v = [rng.randrange(8) for _ in range(4)]
        if any(v): break
    if symp:                      # x -> x + lam * Bf(x, v) * v  (symplectic)
        lam = rng.randrange(1, 8)
        coef = [mul[lam][Bf(tuple(1 if k == j else 0 for k in range(4)), tuple(v))] for j in range(4)]
        return [[(1 if i == j else 0) ^ mul[coef[j]][v[i]] for j in range(4)] for i in range(4)]
    while True:                   # general x -> x + lam * w.x * v (invertible unless 1 = lam*w.v)
        w = [rng.randrange(8) for _ in range(4)]; lam = rng.randrange(1, 8)
        T = [[(1 if i == j else 0) ^ mul[mul[lam][w[j]]][v[i]] for j in range(4)] for i in range(4)]
        if matinv(T) is not None: return T


def move_M(st, symp):
    s2 = cp(st); s2["M"] = matmul(transvection(symp), st["M"]); return s2


def move_h(st):
    k = rng.randrange(KS); usedL, usedP = other_sets(st, k)
    M = st["M"]; _, Cinv = CC(M)
    h = rand_h()
    r = greedy_switch(h, usedL, usedP, Cinv)
    if r is None: return None
    om, ps = r; s2 = cp(st); s2["h"][k] = h; s2["om"][k] = om; s2["ps"][k] = ps; s2["R9"][k] = h[om]
    return s2


def save_state(st, cost, tag):
    with open(os.path.join(OUTDIR, f"{tag}_state.json"), "w") as f:
        json.dump({"cost": cost, "state": st}, f)
    b = build(st)
    if b is not None:
        write_file(b, os.path.join(OUTDIR, f"{tag}_start.in"))


def main():
    t0 = time.time()
    best = None; best_cost = None
    for t in range(INIT_TRIES):
        st = init_state()
        if st is None: continue
        c = cost_of(st)
        if c is None: continue
        if best_cost is None or c < best_cost:
            best, best_cost = st, c
    print(f"init best {best_cost} after {INIT_TRIES} tries, {time.time()-t0:.1f}s", flush=True)
    cur, cur_cost = best, best_cost
    start_cost = best_cost
    best_saved = best_cost
    tstart = time.time(); it = 0; acc = 0
    stats = {}
    while time.time() - tstart < SECS:
        frac = (time.time() - tstart) / SECS
        T = T0 * (T1 / T0) ** frac
        r = rng.random()
        if r < 0.40: name, st2 = "p", move_p(cur)
        elif r < 0.55: name, st2 = "om", move_om(cur)
        elif r < 0.75: name, st2 = "R9", move_R9(cur)
        elif r < 0.93: name, st2 = "Msymp", move_M(cur, True)
        elif r < 0.98: name, st2 = "Mgen", move_M(cur, False)
        else: name, st2 = "h", move_h(cur)
        it += 1
        if st2 is None: continue
        c2 = cost_of(st2)
        if c2 is None: continue
        d = c2 - cur_cost
        s = stats.setdefault(name, [0, 0]); s[0] += 1
        if d <= 0 or rng.random() < math.exp(-d / T):
            cur, cur_cost = st2, c2; acc += 1; s[1] += 1
            if c2 < best_cost:
                best, best_cost = st2, c2
                if best_cost < best_saved - 0:
                    save_state(best, best_cost, "best"); best_saved = best_cost
    save_state(best, best_cost, "best")
    b = build(best); validate(b)
    print(f"iters {it} scored {NSCORE[0]} accepted {acc} start_cost {start_cost} best_cost {best_cost} "
          f"T_end {T:.2f} time {time.time()-t0:.1f}s", flush=True)
    print("moves (tried, accepted):", stats, flush=True)


if __name__ == "__main__":
    main()
