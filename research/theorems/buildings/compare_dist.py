"""Compare BFS distance layers of real flag graphs (polar_flags.py, built from the definition) with the
Weyl-group prediction (weyl_dist.py).  Every vertex's layers must equal the prediction for its side.
usage: python3 compare_dist.py  (runs the case list below; prints one line per case and side)"""
import subprocess, sys, ast, re
sys.path.insert(0, '.')
from weyl_dist import predict

CASES = [  # (geometry args, Weyl type, rank, params per reflection class)
    ("PG 2 2", 'A', 2, [2]), ("PG 2 3", 'A', 2, [3]), ("PG 3 2", 'A', 3, [2]), ("PG 3 3", 'A', 3, [3]),
    ("PG 4 2", 'A', 4, [2]), ("PG 4 3", 'A', 4, [3]), ("PG 5 2", 'A', 5, [2]),
    ("Sp 2 2", 'B', 2, [2, 2]), ("Sp 2 3", 'B', 2, [3, 3]), ("O 2 3", 'B', 2, [3, 3]),
    ("Sp 3 2", 'B', 3, [2, 2]), ("Sp 3 3", 'B', 3, [3, 3]), ("O 3 3", 'B', 3, [3, 3]), ("Sp 4 2", 'B', 4, [2, 2]),
    ("Om 2 2", 'B', 2, [2, 4]), ("Om 2 3", 'B', 2, [3, 9]), ("Om 3 2", 'B', 3, [2, 4]),
    ("U 4 4", 'B', 2, [4, 2]), ("U 5 4", 'B', 2, [4, 8]), ("U 6 4", 'B', 3, [4, 2]),
    ("Op 4 2", 'D', 4, [2]),
]
allok = True
for g, t, r, params in CASES:
    p = subprocess.run(["python3", "polar_flags.py"] + g.split(), capture_output=True, text=True, timeout=7200)
    lines = p.stdout.strip().splitlines()
    head = lines[0]
    m = re.search(r"vertices (\d+) \(odd-dim flags (\d+), even-dim flags (\d+)\), degrees odd \[(\d+)\] even \[(\d+)\]", head)
    nv, No, Ne, dodd, deven = map(int, m.groups())
    lay = {}
    for L in lines[1:]:
        side = 'odd' if 'from odd' in L else 'even'
        same = 'identical layers: True' in L
        lay[side] = (ast.literal_eval(L[L.index('{'):]), same)
    C, I, cls, E, out, W, prm = predict(t, r, params)
    # predicted combined layers for a source that is a residue of type I[J]
    pred = {}
    for J in (0, 1):
        comb = {}
        for K in (0, 1):
            for d, c in out[(J, K)].items(): comb[d] = comb.get(d, 0) + c
        deg = comb[1]
        pred[J] = dict(sorted(comb.items()))
    ok_case = True
    for side, deg in (('odd', dodd), ('even', deven)):
        L, same = lay[side]
        match = [J for J in (0, 1) if pred[J] == L]
        ok = bool(match) and same
        ok_case &= ok
        print(f"{g:8s} ({t}{r}, q={params}) {side:4s}-dim flags: degree {deg:3d}, layers {L}  "
              f"prediction {'MATCH (residue type I%d)' % (match[0] + 1) if match else 'NO MATCH ' + str(pred)}"
              f"{'' if same else '  [sources differ!]'}")
    ecc = max(max(lay['odd'][0]), max(lay['even'][0]))
    print(f"{'':8s} chambers {E}, vertices {nv}, diameter (max eccentricity) {ecc}, Coxeter number h of {t}{r}: "
          f"{ {'A': r + 1, 'B': 2 * r, 'D': 2 * r - 2}[t] }  {'OK' if ok_case else 'FAIL'}")
    allok &= ok_case
print("ALL MATCH" if allok else "SOME MISMATCH")
