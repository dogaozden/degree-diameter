"""Perfect whisker sets by SAT (CaDiCaL via python-sat).
Given H(q) (hex/hex_q{q}.bin), the spread S (runs/S_q{q}_s{seed}.txt, first line = v) and a set B of spread lines
(a file; may be empty), find W: one whisker at every point of every spread line outside B and v, covering every free
point (off S, not on a line meeting v) exactly once.  Usage: sat_w.py q seed Bfile outW [seconds]"""
import collections, sys, time
from hexbin import load
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

q, seed, bfile, outw = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
_, N, lines, crd = load(q)
lines = lines.tolist()
S = [int(x) for x in open(f'runs/S_q{q}_s{seed}.txt').read().split()]
v = S[0]
B = set(int(x) for x in open(bfile).read().split()) if bfile != '-' else set()
Sset = set(S)
spt = {}
for s in S:
    for p in lines[s]:
        spt[p] = s
thr = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        thr[p].append(k)
vlines = set(k for p in lines[v] for k in thr[p])
blocked = set(p for k in vlines for p in lines[k]) - set(spt)
free = [p for p in range(N) if p not in spt and p not in blocked]
cand = []
for k, L in enumerate(lines):
    if k in Sset or k in vlines:
        continue
    sp = [p for p in L if p in spt]
    if len(sp) != 1:
        raise SystemExit('line meets S not once')
    s = spt[sp[0]]
    if s == v or s in B or any(p in blocked for p in L):
        continue
    cand.append(k)
var = {k: i + 1 for i, k in enumerate(cand)}
bypt = collections.defaultdict(list)
byspt = collections.defaultdict(list)
for k in cand:
    for p in lines[k]:
        (byspt if p in spt else bypt)[p].append(var[k])
Apts = [p for s in S if s != v and s not in B for p in lines[s]]
print(f'q={q} free={len(free)} candidates={len(cand)} A-points={len(Apts)} need {len(free)//q}', flush=True)
solver = Cadical153()
top = len(cand)
nclauses = 0
for groups in (bypt, byspt):
    keys = free if groups is bypt else Apts
    for p in keys:
        lits = groups.get(p, [])
        if not lits:
            raise SystemExit(f'point {p} has no candidate')
        solver.add_clause(lits)
        enc = CardEnc.atmost(lits, 1, top_id=top, encoding=EncType.seqcounter if len(lits) > 6 else EncType.pairwise)
        top = max(top, enc.nv)
        for c in enc.clauses:
            solver.add_clause(c)
        nclauses += 1 + len(enc.clauses)
print('clauses', nclauses, flush=True)
t = time.time()
ok = solver.solve()
print('SAT' if ok else 'UNSAT', f'{time.time()-t:.1f}s', flush=True)
if ok:
    model = set(l for l in solver.get_model() if l > 0)
    W = [k for k in cand if var[k] in model]
    open(outw, 'w').write('\n'.join(map(str, W)) + '\n')
    print('whiskers', len(W), '->', outw)
