"""Best known per cell (ours vs DS14v2 table vs bipartite Moore bound), Δ = 3..16, D = 3..10.
Ours: Haar records in research/frontier/sols (records.json), plus the non-Haar results listed in research/RESULTS.md
and research/lifts (typed in below), plus (16,5) 31,460 (flags.py)."""
import json, sys
sys.path.insert(0, '../frontier')
from heuristic import TABLE, moore
ours = {}
for r in json.load(open('records.json')):
    k = (r['d'], r['D']); ours[k] = max(ours.get(k, 0), r['vertices'])
extra = {(11,3):192,(13,3):276,(15,3):376,(16,3):396,(7,4):359,(11,4):1782,(13,4):3146,(15,4):5070,(16,4):5440,
         (4,5):162,(5,5):354,(7,5):1152,(8,5):1764,(9,5):2662,(16,5):31460,
         (7,6):9592,(11,6):148944,(13,6):388972,(15,6):870440,(16,6):940846,
         (3,8):288,(5,8):9324,(5,9):28842,(5,10):95472,(4,10):12246}
for k, v in extra.items(): ours[k] = max(ours.get(k, 0), v)
print("best/Moore per cell (ours if we hold it, marked *; else the table value)")
print("Δ\\D " + " ".join(f"{D:>7}" for D in range(3, 11)))
for d in range(3, 17):
    row = []
    for D in range(3, 11):
        t = TABLE[d][D - 3]; o = ours.get((d, D), 0)
        b = max(t or 0, o)
        row.append(f"{b/moore(d,D):6.3f}{'*' if o > (t or 0) else ' '}")
    print(f"{d:>3} " + " ".join(row))
