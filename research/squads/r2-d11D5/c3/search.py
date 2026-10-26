#!/usr/bin/env python3
"""c3 (card of squad r2-d11D5): search over regulus-switch starts.

Switch (as in d11D5/plus/mkreg.py): h = hyperbolic line of hcand.json, L_j = delta(R_j) (9 regulus lines), transversal
t_k of the 9 transversals (each meets all L_j), p_j = L_j ∩ t_{pi(j)}, y_j = L_j ∩ t_tau, sigma = delta with the swaps
sigma(p_j)<->sigma(y_j) and sigma(delta(L_j))<->sigma(delta(m_j)), m_j = the mch[j]-th line through p_j other than L_j.
New in this card: pi may be a bijection onto all 9 transversals ('perm'), or a bijection with no collinear p-pair ('ovoid'),
or the mkreg rule ('mk'). Each start is scored by plusopt5 (SCORE=1). Usage: python3 search.py SECS seed"""
import json, random, subprocess, sys, time, os

HERE = os.path.dirname(os.path.abspath(__file__))
D11 = "/home/user/degree-diameter/research/d11D5"
SCORER = os.path.join(HERE, "plusopt5")
SECS = float(sys.argv[1]) if len(sys.argv) > 1 else 400
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = random.Random(SEED)
ENV = dict(os.environ, SCORE="1")

W = json.load(open(os.path.join(D11, "w8.json")))
n = len(W["points"]); L = [list(s) for s in W["lines"]]
m_pol = W["polarity_m"] if W["polarity_m"] is not None else 0
def pw(perm, k):
    r = list(range(n))
    for _ in range(k): r = [perm[x] for x in r]
    return r
fpm, flm = pw(W["frob_pt"], m_pol), pw(W["frob_ln"], m_pol)
d_pt = [W["klein_pt"][fpm[x]] for x in range(n)]     # point -> line (delta)
d_ln = [W["klein_ln"][flm[x]] for x in range(n)]     # line -> point (delta)
cand = json.load(open(os.path.join(D11, "plus", "hcand.json")))
Lset = [set(s) for s in L]
pl = [[m for m in range(n) if p in L[m]] for p in range(n)]
col = [set() for _ in range(n)]
for s in L:
    for a in s: col[a].update(s)
TSETS = [[set(t) for t in c["trans"]] for c in cand]

def build(hi, pi, tau, mch):
    c = cand[hi]; lines = c["L"]; ts = TSETS[hi]
    pts = [next(iter(Lset[lines[j]] & ts[pi[j]])) for j in range(9)]
    ys = [next(iter(Lset[lines[j]] & ts[tau])) for j in range(9)]
    Lb = [list(s) for s in L]; X = n
    for p, l in zip(pts, lines): Lb[l].remove(p); Lb[l].append(X)
    Lb.append(pts[:])
    sig = d_pt[:] + [n]; pos = {l: i for i, l in enumerate(sig)}
    def swap(a, b):
        sig[a], sig[b] = sig[b], sig[a]; pos[sig[a]] = a; pos[sig[b]] = b
    for j in range(9):
        p, y, l = pts[j], ys[j], lines[j]
        if y != p: swap(p, y)
        ms = [m for m in pl[p] if m != l]
        swap(pos[l], pos[ms[mch[j]]])
    ncol = sum(1 for i in range(9) for j in range(i + 1, 9) if pts[j] in col[pts[i]])
    return Lb, sig, ncol

_cnt = [0]
def score(hi, pi, tau, mch, keep=None):
    Lb, sig, ncol = build(hi, pi, tau, mch)
    fn = os.path.join(HERE, "tmp_%d.in" % SEED)
    with open(fn, "w") as g:
        g.write(f"{n+1} 9\n")
        for s in Lb: g.write(" ".join(map(str, s)) + "\n")
        g.write("\n".join(map(str, sig)) + "\n")
    out = subprocess.run([SCORER, fn], env=ENV, capture_output=True, text=True, timeout=60).stdout
    cost = int(out.split("cost=")[1].split()[0]); _cnt[0] += 1
    if keep: os.replace(fn, keep)
    return cost, ncol

def sample(mode):
    hi = rng.randrange(len(cand))
    if mode == "mk":
        tau = rng.randrange(9); others = [k for k in range(9) if k != tau]; rng.shuffle(others)
        pi = [others[j % 8] for j in range(9)]
    elif mode == "perm":
        pi = list(range(9)); rng.shuffle(pi); tau = rng.randrange(9)
    else:  # ovoid: bijection with no collinear p-pair (rejection)
        while True:
            pi = list(range(9)); rng.shuffle(pi); tau = rng.randrange(9)
            pts = [next(iter(Lset[cand[hi]["L"][j]] & TSETS[hi][pi[j]])) for j in range(9)]
            if not any(pts[j] in col[pts[i]] for i in range(9) for j in range(i + 1, 9)): break
    mch = [rng.randrange(8) for _ in range(9)]
    return hi, pi, tau, mch

def neighbour(cfg):
    hi, pi, tau, mch = cfg; pi = pi[:]; mch = mch[:]
    r = rng.random()
    if r < 0.4:
        j, k = rng.randrange(9), rng.randrange(9); pi[j], pi[k] = pi[k], pi[j]
    elif r < 0.55:
        pi[rng.randrange(9)] = rng.randrange(9)
    elif r < 0.7:
        tau = rng.randrange(9)
    else:
        mch[rng.randrange(9)] = rng.randrange(8)
    return hi, pi, tau, mch

t0 = time.time(); pool = []
per_mode = {}
phase1_end = t0 + SECS * 0.6
modes = ["mk", "perm", "ovoid"]
k = 0
while time.time() < phase1_end:
    mode = modes[k % 3]; k += 1
    cfg = sample(mode); c, ncol = score(*cfg)
    pool.append((c, mode, ncol, cfg))
    per_mode.setdefault(mode, []).append(c)
pool.sort(key=lambda x: x[0])
print("phase1 samples", len(pool), "time", round(time.time() - t0), flush=True)
for mode in modes:
    v = sorted(per_mode.get(mode, []))
    if v: print(mode, "n", len(v), "min", v[0], "median", v[len(v)//2], "10pct", v[len(v)//10], flush=True)
print("top 12 phase1:", [(c, m, nc) for c, m, nc, _ in pool[:12]], flush=True)

# phase 2: randomised local search (sideways moves allowed) from the best distinct starts
seen = set(); starts = []
for item in pool:
    key = (item[3][0], tuple(item[3][1]), item[3][2], tuple(item[3][3]))
    if key in seen: continue
    seen.add(key); starts.append(item)
    if len(starts) >= 8: break
best_found = []
for c0, mode, ncol, cfg in starts:
    if time.time() > t0 + SECS: break
    cur, curc = cfg, c0
    for step in range(120):
        if time.time() > t0 + SECS: break
        nb = neighbour(cur); c, nc = score(*nb)
        if c <= curc: cur, curc = nb, c
    best_found.append((curc, mode, cur))
    print("local search from", c0, "->", curc, flush=True)
allres = sorted([(c, m, nc, cfg) for c, m, nc, cfg in pool] + [(c, m, -1, cfg) for c, m, cfg in best_found], key=lambda x: x[0])
top = []; keys = set()
for c, m, nc, cfg in allres:
    key = (cfg[0], tuple(cfg[1]), cfg[2], tuple(cfg[3]))
    if key in keys: continue
    keys.add(key); top.append((c, m, nc, cfg))
    if len(top) >= 3: break
res = []
for rank, (c, m, nc, cfg) in enumerate(top):
    fn = os.path.join(HERE, "top", "s%d_r%d.in" % (SEED, rank))
    cc, _ = score(*cfg, keep=fn)
    res.append({"rank": rank, "cost": cc, "mode": m, "ncol": nc, "hi": cfg[0], "pi": cfg[1], "tau": cfg[2], "mch": cfg[3], "file": fn})
    print("TOP", rank, "cost", cc, "mode", m, "ncol", nc, "hi", cfg[0], "pi", cfg[1], "tau", cfg[2], "mch", cfg[3], "file", fn, flush=True)
json.dump({"seed": SEED, "evals": _cnt[0], "phase1": [(c, m, nc) for c, m, nc, _ in pool[:50]], "top": res},
          open(os.path.join(HERE, "results_s%d.json" % SEED), "w"), indent=1)
print("evals", _cnt[0], "total time", round(time.time() - t0), flush=True)
