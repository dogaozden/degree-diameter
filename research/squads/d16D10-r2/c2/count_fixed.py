#!/usr/bin/env python3
# Count the alpha-fixed uncovered elements in an EVAL UNCPRINT=1 output file.
# alpha = (conjugation by g) x (z -> r z) on SL(2,61) x Z_10141 with g = mat(0,60,1,17), r = 7445.
# An uncovered element (x, z) is alpha-fixed iff z = 0 and x commutes with g (the only fixed z is 0).
# usage: python3 count_fixed.py EVAL_OUTPUT_FILE
import re
import sys

P = 61
G = (0, 60, 1, 17)  # g = [[a, b], [c, d]] = mat(0,60,1,17), det 1, order 5


def mul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


pat = re.compile(r"uncovered (\d+) mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\) z=(-?\d+)")
total = 0
fixed = []
for line in open(sys.argv[1]):
    m = pat.search(line)
    if not m:
        continue
    total += 1
    x = tuple(int(m.group(i)) % P for i in range(2, 6))
    z = int(m.group(6))
    if z == 0 and mul(x, G) == mul(G, x):
        fixed.append(line.strip())
print("uncovered_listed", total, "alpha_fixed", len(fixed), "free", total - len(fixed))
for l in fixed:
    print("  fixed:", l)
