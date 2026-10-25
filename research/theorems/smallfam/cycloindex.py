"""Largest multiplier index c = (p-1)/o that the fibre bound allows, per D: p <= B(k,o)/k and p = c*o + 1, so
c <= (B(k,o)/k - 1)/o.  Reads runs/cyclotable_fiber_d3D{D}.txt (k o B ...).  Usage: python3 cycloindex.py FILES"""
import sys
for fn in sys.argv[1:]:
    best = []
    for line in open(fn):
        f = line.split()
        if line.startswith('#') or len(f) < 3:
            continue
        k, o, B = int(f[0]), int(f[1]), int(f[2])
        cmax = (B // k - 1) // o
        best.append((cmax, k, o, B))
    best.sort(reverse=True)
    top = best[:6]
    # also: largest index allowed among (k, o) with o >= 5 (the control used in section 3.2 of the first session)
    big = [x for x in best if x[2] >= 5][:3]
    print(f'{fn}: max allowed index {top[0][0]} at (k, o) = {top[0][1:3]}; top: {top}; with o >= 5: {big}')
