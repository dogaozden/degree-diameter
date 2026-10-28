#!/usr/bin/env python3
"""usage: gen_lift.py q m LIFTS_FILE : prints the lifted matrices reduced mod q (z reduced mod m)."""
import sys
q, m, f = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
for line in open(f):
    if not line.strip(): continue
    A, B, C, D, z = map(int, line.split())
    print("%d %d %d %d %d" % (A % q, B % q, C % q, D % q, z % m))
