# c4_families.py: r4 and m2 of Lemma 5.4 / Corollary 5.5 computed directly from the three families of W2 and from
# Definition 2.1 (written by the independent reviewer of this note; does not share code with myroutes.py).
# Run: python3 c4_families.py 5 6 7 8   (no argument: the far-pair totals at q = 8, 9).
# Referee's own count of r4 and m2 (Lemma 5.4 families, Corollary 5.5 definition), from Definition 2.1 directly.
import sys
def wiring(pat):
    C = {}
    for bar in 'ub':
        for k in range(5):
            s = set()
            for B, tau in enumerate(pat):
                if bar == 'u':
                    offs = (-1, 1) if tau == 'a' else (3, 4)
                else:
                    offs = (2, 3) if tau == 'a' else (-1, 1)
                for o in offs: s.add(5*B + (k + o) % 5)
            C[(bar, k)] = s
    return C
def analyse(pat, Pbar):
    C = wiring(pat); n = 5*len(pat)
    Pcl = [Y for Y in C if Y[0] == Pbar]; Lcl = [Y for Y in C if Y[0] != Pbar]
    def share(cls, c, d): return any(c in C[Y] and d in C[Y] for Y in cls)
    out = []
    for X in Pcl:
        for cp in range(n):
            if cp in C[X]: continue
            Nset = {c1 for c1 in C[X] if share(Lcl, c1, cp)}
            W = set()
            for c1 in C[X]:
                for c2 in range(n):
                    if c2 == c1: continue
                    if c2 != cp and share(Pcl, c2, c1) and share(Lcl, c2, cp): W.add((cp, c2))      # kind 1
                    if c2 != cp and share(Lcl, c1, c2) and share(Lcl, c2, cp): W.add((cp, c1))      # kind 2
                    if c2 != cp and share(Lcl, c1, c2) and share(Pcl, c2, cp): W.add((c2, c1))      # kind 3
            m2 = len(W - {(cp, c1) for c1 in Nset})
            out.append((X, cp, len(Nset), m2))
    return out
for alpha in map(int, sys.argv[1:]):
    worst_best = 0; worst_best_pt = 0
    for na in range(alpha + 1):
        pat = 'a'*na + 'b'*(alpha - na)
        res = {}
        for Pbar in 'ub':
            o = analyse(pat, Pbar)
            st = [m2 for (_, _, r4, m2) in o if r4 == alpha]
            res[Pbar] = (min(r4 for (_, _, r4, _) in o), len(st), min(st), max(st))
        best_both = min(res['u'][2], res['b'][2]); worst_best = max(worst_best, best_both)
        worst_best_pt = max(worst_best_pt, res['u'][2], res['b'][2])
        print(alpha, pat, "unbarred-as-point-bar: min r4 %d, starved %d, m2 %d..%d" % res['u'], "| barred-as-point-bar: min r4 %d, starved %d, m2 %d..%d" % res['b'])
    print("alpha", alpha, "worst pattern, best pair over both bars:", worst_best, "; worst over (pattern, reading) of best point-bar pair:", worst_best_pt)

# totals: point bar only vs both bars (starved pairs only, as in the note)
def totals(q, alpha):
    N = (q**6-1)//(q-1); rows = []
    for na in range(alpha+1):
        pat = 'a'*na + 'b'*(alpha-na)
        per = {}
        for Pbar in 'ub':
            per[Pbar] = sum(N*(q**5 - alpha*q**4 - m2*q*q) for (_, _, r4, m2) in analyse(pat, Pbar) if r4 == alpha)
        rows.append((pat, per['u'], per['b'], per['u'] + per['b']))
    return rows
if len(sys.argv) == 1:
    for q, a in ((8, 5), (9, 6)):
        rows = totals(q, a)
        for r in rows: print(q, r[0], "%.4g %.4g both %.4g" % r[1:])
        print(q, "min both bars %.4g; min point-bar-only %.4g" % (min(r[3] for r in rows), min(min(r[1], r[2]) for r in rows)))
