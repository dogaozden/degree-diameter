"""Exhaustive cyc sweep: labels (1, t2) on the two 3-cycles of LPS(p) x Z_m, all t2 in Z_m, every root r of r^2+r+1 (up to 2).
Usage: sweep_cyc.py p q D m1,m2,...   -> appends JSON lines to results_cyc.jsonl (cost = unreached within D from both starts; 0 = diam <= D and FULL)."""
import sys, json, time
import c5lib as L
p, q, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
ms = [int(t) for t in sys.argv[4].split(',')]
lp = L.Lps(p, q)
out = open('results_cyc.jsonl', 'a')
TAB = {8: 201480, 9: 1091232}
for m in ms:
    V = L.V_of(q, m)
    roots = lp.roots(m)[:2]
    for rk, r in enumerate(roots):
        best = None
        t0 = time.time()
        for t2 in range(0, m):
            labs = lp.cyc_labels(m, r, [1, t2])
            c, diam, cA, cB, _ = L.cost(lp, q, m, labs, D)
            if best is None or c < best[0]: best = (c, t2, diam, cA, cB)
            if c == 0:
                rec = dict(p=p, q=q, m=m, V=V, rule='cyc', r=r, t2=t2, cost=0, diam=diam, D=D, ts=[1, t2])
                out.write(json.dumps(rec) + '\n'); out.flush()
        rec = dict(p=p, q=q, m=m, V=V, rule='cyc', r=r, best_cost=best[0], best_t2=best[1], diam=best[2], cA=best[3],
                   cB=best[4], vs_table=round(V / TAB[D], 4), secs=round(time.time() - t0, 1))
        out.write(json.dumps(rec) + '\n'); out.flush()
        print(rec, flush=True)
