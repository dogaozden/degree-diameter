"""Item 5: one formula across the table.  B(H): parts V(H)x{0,1}, x0 ~ y1 iff x = y or xy in E(H).
If H has max degree Δ-1 and diameter D-1 then B(H) is bipartite, max degree Δ, diameter <= D, order 2|H|.
So n_b(Δ, D) >= 2 n(Δ-1, D-1).  Compare 2 n(Δ-1, D-1) (general table, Wikipedia, as of 14 Oct 2026) with the
bipartite table (DS14v2, research/frontier/TABLE.md) and with our best records (research/frontier/sols, flags)."""
import sys, os, json
sys.path.insert(0, '../frontier')
from heuristic import TABLE, moore
from general_table import general_table
G = general_table()
best = {}
for r in json.load(open('records.json')):
    k = (r['d'], r['D']); best[k] = max(best.get(k, 0), r['vertices'])
best[(16, 5)] = max(best.get((16, 5), 0), 31460)   # C(2,3), flags.py
print("cell | bipartite table | ours | 2 n(Δ-1,D-1) | ratio to max(table, ours)")
hits = []
for D in range(3, 11):
    for d in range(4, 17):
        t = TABLE[d][D - 3]
        g = G.get(d - 1, [None]*9)[D - 1 - 2] if D - 1 >= 2 else None
        if g is None or t is None: continue
        b = 2 * g
        ref = max(t, best.get((d, D), 0))
        flag = '  <-- above' if b > ref else ''
        if b > ref: hits.append((d, D, b, t, best.get((d, D))))
        print(f"({d},{D}) | {t:,} | {best.get((d,D),0):,} | {b:,} | {b/ref:.3f}{flag}")
print("\ncells where 2 n(Δ-1,D-1) beats both the bipartite table and our records:", hits)
