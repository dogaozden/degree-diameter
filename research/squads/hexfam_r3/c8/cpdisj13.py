"""c8: disjoint-neighbourhood CP-SAT over a pool of candidate pairs (x,s), q=13.
Chosen pairs must have pairwise disjoint N(x) cap R, pairwise opposite x's and s's, and the cell counts
(R-cell {p}: a_p <= free lines hit exactly by p; R-cell empty: |R| - sum a <= free lines with no hit) hold.
usage: cpdisj13.py POOLX NS TIME OUT"""
import sys, time, numpy as np
from ortools.sat.python import cp_model
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
t0 = time.time(); q = 13
NX, NS, TL, OUT = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
rng = np.random.default_rng(7)
G = Geo(q); N, L = G.N, G.L; LP, PL = G.LP, G.PL
R = np.array([int(v) for v in open('/home/user/degree-diameter/research/d10D7/sets/P13_E7sub_E6_792.txt').read().split()])
Sp = np.array([int(v) for v in open('/home/user/degree-diameter/research/d10D7/sets/L13_spread.txt').read().split()])
inR = np.zeros(N, bool); inR[R] = True; inSp = np.zeros(L, bool); inSp[Sp] = True
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True
cand = np.nonzero(~inR & ~collR)[0]
a = np.zeros(len(cand), np.int64)
for i in range(0, len(cand), 20000):
    a[i:i+20000] = (G.B(G.C[cand[i:i+20000]], G.C[R]) == 0).sum(1)
print('non-collinear candidates', len(cand), 'a-hist min/25%/50%:', a.min(), np.percentile(a, 25), np.median(a), flush=True)
order = np.argsort(a, kind='stable')
xs = cand[order[:NX*3]]; xs = xs[rng.permutation(len(xs))][:NX]
def l4(s):
    M = PL[LP[s]].ravel(); M = M[M != s]
    m = np.zeros(L, bool); m[PL[LP[M]].ravel()] = True; return m, M
# candidate lines: random non-spread lines, with their Sp-hit set and conc line
ls = rng.choice(np.nonzero(~inSp)[0], size=NS * 4, replace=False)
info = []
for s in ls:
    m, M = l4(int(s)); cm = M[inSp[M]]
    hit = np.nonzero(m & inSp)[0]
    conc = int(cm[0]) if len(cm) == 1 else -1
    if len(cm) > 1: continue
    hit = hit[hit != conc]
    info.append((int(s), hit, conc, m))
    if len(info) >= NS: break
print('lines usable', len(info), 'mean hits', np.mean([len(h) for _, h, _, _ in info]), flush=True)
pairs = []   # (xi, s_index-in-info, x, a_x, Rnb set, s, hit, conc)
Rnb = {}
for x in xs:
    nb = np.nonzero(G.B(G.C[[x]], G.C[R])[0] == 0)[0]
    Rnb[int(x)] = nb
xs_list = [int(x) for x in xs]
# choose for each x a random subset of lines (all lines, pool size = NX*len) -- restrict to 4 per x
K_PER = 4
for x in xs_list:
    idx = rng.choice(len(info), size=min(K_PER, len(info)), replace=False)
    for j in idx: pairs.append((x, j))
n = len(pairs); print('pool pairs', n, flush=True)
xo = np.array([p[0] for p in pairs]); 
# opposite tests
Bx = G.B(G.C[xs_list], G.C[xs_list]) != 0
xi = {x: i for i, x in enumerate(xs_list)}
m = cp_model.CpModel(); z = [m.NewBoolVar('z%d' % i) for i in range(n)]
byx = {}
for i, (x, j) in enumerate(pairs): byx.setdefault(x, []).append(i)
for x, lst in byx.items(): m.Add(sum(z[i] for i in lst) <= 1)
# R-disjointness
byr = {}
for i, (x, j) in enumerate(pairs):
    for r in Rnb[x]: byr.setdefault(int(r), []).append(i)
for r, lst in byr.items():
    if len(lst) > 1: m.Add(sum(z[i] for i in lst) <= 1)
# x pairwise opposite
for i in range(n):
    for k in range(i + 1, n):
        xa, xb = pairs[i][0], pairs[k][0]
        if xa == xb: continue
        if not Bx[xi[xa], xi[xb]]: m.AddBoolOr([z[i].Not(), z[k].Not()])
# s pairwise opposite
for i in range(n):
    for k in range(i + 1, n):
        si, sk = info[pairs[i][1]][0], info[pairs[k][1]][0]
        if pairs[i][1] == pairs[k][1] or info[pairs[i][1]][3][sk]: m.AddBoolOr([z[i].Not(), z[k].Not()])
# line cells
hitters = {}; conc_of = {}
for i, (x, j) in enumerate(pairs):
    s, hit, conc, _ = info[j]
    for l in hit: hitters.setdefault(int(l), []).append(i)
    if conc >= 0: conc_of.setdefault(conc, []).append(i)
lines = sorted(set(hitters) | set(conc_of))
Ax = {x: len(Rnb[x]) for x in xs_list}
o_terms = {i: [] for i in range(n)}; g_terms = []; const_empty = int(((~inSp)&False).sum())
e = {}
for l in lines:
    H = hitters.get(l, []); M = len(H)
    el = m.NewBoolVar('e%d' % l); e[l] = el
    if M:
        m.Add(sum(z[i] for i in H) <= 1 + M * (1 - el))
    for i in conc_of.get(l, []): m.AddImplication(z[i], el.Not())
    for i in H:
        o = m.NewBoolVar('');
        m.AddImplication(o, z[i]); m.AddImplication(o, el); o_terms[i].append(o)
    g = m.NewBoolVar('')
    if M: m.Add(M * g + sum(z[i] for i in H) <= M)
    m.AddImplication(g, el.Not()) if False else None
    m.AddImplication(g, el.Not())   # empty means not hit-once; keep g and e exclusive
    for i in conc_of.get(l, []): m.AddImplication(z[i], g.Not())
    g_terms.append(g)
for i in range(n):
    x = pairs[i][0]
    if o_terms[i]:
        m.Add(sum(o_terms[i]) >= Ax[x] * z[i])
    else:
        m.Add(z[i] == 0) if Ax[x] > 0 else None
# total empty-cell lines available: lines not hit by anything are constant free (except conc lines of chosen)
nb_lines = len(Sp) - len(lines)
m.Add(sum(g_terms) + nb_lines >= len(R) - sum(Ax[pairs[i][0]] * z[i] for i in range(n)))
m.Maximize(sum(z))
sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = TL; sol.parameters.num_workers = 1
st = sol.Solve(m)
print('status', sol.StatusName(st), 'obj', sol.ObjectiveValue() if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None, 'bound', sol.BestObjectiveBound(), 'time %.0f' % (time.time()-t0), flush=True)
if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): sys.exit(0)
chosen = [pairs[i] for i in range(n) if sol.Value(z[i])]
X = [p[0] for p in chosen]; S = [info[p[1]] for p in chosen]
print('chosen', len(chosen), 'sizes', [Ax[x] for x in X], flush=True)
# build R -> free line matching cell by cell
pat_R = {int(r): frozenset(k for k, x in enumerate(X) if r in set(Rnb[x].tolist())) for r in R}
removed = set(int(c) for _, _, c, _ in S if c >= 0)
hitsets = {}
for k, (s, hit, conc, mm) in enumerate(S):
    for l in hit: hitsets.setdefault(int(l), set()).add(k)
pat_L = {}
freeL = [int(l) for l in Sp if int(l) not in removed]
for l in freeL: pat_L.setdefault(frozenset(hitsets.get(l, set())), []).append(l)
from collections import defaultdict
byc = defaultdict(list)
for r in R: byc[pat_R[int(r)]].append(int(r))
ok = True; out = []
for T, rs in byc.items():
    ls_ = pat_L.get(T, [])
    if len(ls_) < len(rs): ok = False; print('cell fail', sorted(T), len(rs), len(ls_)); break
    for r, l in zip(rs, ls_): out.append((r, l))
if ok:
    for x, (s, hit, conc, mm) in zip(X, S): out.append((x, s))
    open(OUT, 'w').write('\n'.join('%d %d' % p for p in out) + '\n')
    print('wrote', OUT, len(out), flush=True)
