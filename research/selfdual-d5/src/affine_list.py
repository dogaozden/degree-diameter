#!/usr/bin/env python3
"""affine_list.py LO HI: groups F_p^d : C_k (d = 2, 3, 4) of order p^d k in [LO, HI], y acting by an element R of order
o of a Singer cycle (o | k, o | p^d - 1, o >= 3, R irreducible: o divides no p^j - 1, j < d proper divisor of d).
Lines "n p d k E o" with R = C^E, E = (p^d - 1) / o; sorted by n, then by k / o (the order of the kernel <y^o>)."""
import sys
lo, hi = int(sys.argv[1]), int(sys.argv[2])
primes = [p for p in range(3, 200) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
rows = []
for p in primes:
    for d in (2, 3, 4):
        q = p ** d
        if q > hi: continue
        for k in range(3, hi // q + 1):
            n = q * k
            if n < lo: continue
            for o in range(3, k + 1):
                if k % o or (q - 1) % o: continue
                if any((p ** j - 1) % o == 0 for j in range(1, d) if d % j == 0): continue
                rows.append((n, k // o, p, d, k, (q - 1) // o, o))
rows.sort()
for n, c, p, d, k, E, o in rows: print(n, p, d, k, E, o)
