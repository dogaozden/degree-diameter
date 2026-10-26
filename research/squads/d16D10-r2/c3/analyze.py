# card c3 analysis helper: parses run.log / run.out / eval.out in this folder (no writes except the printed summary).
import re, os, json
D = os.path.dirname(os.path.abspath(__file__))
def rd(f):
    p = os.path.join(D, f)
    return open(p).read() if os.path.exists(p) else ""
log, out, ev = rd('run.log'), rd('run.out'), rd('eval.out')
g = re.search(r'group (sl|psl) (\d+) x Z_(\d+)', log)
fam, p, NC = g.group(1), int(g.group(2)), int(g.group(3))
al = re.search(r'alpha: conj by mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\), z -> (-?\d+) z on Z_(\d+) \(fixed z: (\d+)\)', log)
A, B, C, Dd = map(int, al.group(1, 2, 3, 4)); AR = int(al.group(5)); NCa = int(al.group(6)); nfixz = int(al.group(7))
assert NCa == NC
HALF = (p - 1) // 2
def canon(a, b, c, d):
    if fam == 'psl':
        f = a if a else c
        if f > HALF: a, b, c, d = (-a) % p, (-b) % p, (-c) % p, (-d) % p
    return (a, b, c, d)
def mul(x, y):
    return ((x[0]*y[0] + x[1]*y[2]) % p, (x[0]*y[1] + x[1]*y[3]) % p, (x[2]*y[0] + x[3]*y[2]) % p, (x[2]*y[1] + x[3]*y[3]) % p)
G = (A, B, C, Dd); Gi = ((Dd) % p, (-B) % p, (-C) % p, (A) % p)
# alpha-fixed: z-part fixed by z -> AR z, and matrix commutes with g (projectively for PSL)
def alpha_fixed(a, b, c, d, z):
    conj = canon(*mul(mul(G, (a, b, c, d)), Gi))
    return conj == canon(a, b, c, d) and (AR * z - z) % NC == 0
# search log
steps = [tuple(map(int, m)) for m in re.findall(r't=(\d+) step=(\d+) evals=(\d+) slot=\d+ cand=-?\d+ cost=(-?\d+) best=(-?\d+)', log)]
st = re.search(r'start cost=(\d+)', log)
res = re.search(r'RESULT .* best=(\d+) evals=(\d+) steps=(\d+) time=([\d.]+)', out)
best_final = int(res.group(1)) if res else (min([s[4] for s in steps]) if steps else None)
first_evals = first_step = None
if st and int(st.group(1)) == best_final:
    first_evals, first_step = 1, 0
else:
    for t, step, evals, cost, best in steps:
        if best == best_final:
            first_evals, first_step = evals, step; break
# evaluation of the best S
evc = re.search(r'EVAL \S+ cost=(\d+)', ev)
unc = re.findall(r'uncovered \d+ mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\) z=(-?\d+)', ev)
fixed = sum(1 for u in unc if alpha_fixed(*map(int, u[:4]), int(u[4])))
summary = dict(group=f"{fam} {p} x Z_{NC}", alpha=f"conj by mat({A},{B},{C},{Dd}), z->{AR}z, fixed z {nfixz}",
               run_result=res.group(0) if res else None, best_final=best_final, first_reached_evals=first_evals,
               first_reached_step=first_step, eval_cost=int(evc.group(1)) if evc else None,
               uncovered_listed=len(unc), alpha_fixed_holes=fixed, free_holes=len(unc) - fixed,
               n_steps_logged=len(steps))
print(json.dumps(summary, indent=1))
