"""Evaluate the typing profiles printed by tourn.c: max over regular tournaments and typings of
min(alpha) + min(beta), compared with the formulas claimed in sec. 8 of the note, on a grid of a >= b >= c >= 0."""
import sys, itertools
def load(path):
    lines = open(path).read().split()
    r = None
    keys = [int(x) for x in lines[2:]]
    n = int(lines[0].split('=')[1]); return n, keys
def value(key, n, a, b, c):
    r = (n - 1) // 2; w = r + 1
    al = []; be = []
    for tv in (0, 1):
        for f in range(w):
            if key >> (tv * w + f) & 1:
                al.append(f * (a if tv == 0 else b) + (r - f) * c)
            if key >> (2 * w + tv * w + f) & 1:
                be.append(f * (b if tv == 0 else a) + (r - f) * c)
    return min(al) + min(be)
claims = {5: lambda a, b, c: 2 * b + 2 * c,
          7: lambda a, b, c: min(a + b + 4 * c, 3 * b + 3 * c),
          9: lambda a, b, c: 4 * b + 4 * c}
for path in sys.argv[1:]:
    n, keys = load(path)
    bad = []; tested = 0
    vals = list(range(0, 13)) + [20, 50, 82, 122]
    for a, b, c in itertools.product(vals, repeat=3):
        if not a >= b >= c >= 0:
            continue
        best = max(value(k, n, a, b, c) for k in keys); tested += 1
        if best != claims[n](a, b, c):
            bad.append((a, b, c, best, claims[n](a, b, c)))
    print("n=%d: %d profiles, %d (a,b,c) triples tested, %d disagreements with the claimed formula" %
          (n, len(keys), tested, len(bad)), bad[:8])
