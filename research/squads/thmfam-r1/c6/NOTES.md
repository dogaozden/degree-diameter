# c6: LPS(p=5) x Z_m with omega-equivariant Z_m labels (q = 13, 17, 23, 29)

- gen_c6.py q m t2 rsel: the 6 LPS generators (lps_haar 5 q -v). The two 3-cycles of the quaternion map
  (a0,a1,a2,a3) -> (a0,a3,a1,a2) (conjugation by omega = (1+i+j+k)/2) are computed from the quaternions.
  Cycle 1 labels (1, r, r^2), cycle 2 labels (t2, r t2, r^2 t2), r = rsel-th element of order 3 mod m.
  t1 = 1 WLOG (multiplying all labels by a unit is a graph isomorphism).
- sweep.py q m...: all t2 in [1,m-1] and both r, run haar_ecc pgl q m (exact diameter), append to results.jsonl.
- summarize.py: best (smallest diameter, full component) per (q,m).
- Component check: full means compA = compB = q(q^2-1)m (S lies in one PSL-coset, so the component of (e,A)
  is 2|PSL| m = |PGL| m vertices; for q = 29, (5/29) = +1 so S is in PSL; for q = 13, 17, 23, S is in PGL \ PSL).
- Primes m = 1 mod 3 only (m = 1 has no order-3 element; m = 3 gives r = 1, degenerate).

## Results (exact diameter, full component, all t2 in [1,m-1] and both r; primes m = 1 mod 3 listed)
Best (smallest diameter) per (q,m) is in summarize.py output; full table in results.jsonl.
Best vertices with diam <= D:
- D = 8: (q,m) = (13,13), 28392 vertices (0.953 of 29790), t2 = 2.
- D = 9: (13,43), 93912 vertices (0.800 of 117360), t2 = 2. Also (17,19) 93024, (23,7) 85008.
- D = 10: (23,37), 449328 vertices (0.994 of 452032), t2 = 19. Also (23,31) 376464, (29,13) 316680.
Not reached: (23,43) 522192 has diam 11; (29,19) 462840 has diam 11; (17,37) 181152 has diam 10.
Coverage limits: no sweep for m > 61 at q = 13, m > 37 at q = 17, m = 31, 37 at q = 29 (only t2 = 5 at m = 37 was tried by hand, diam 11).
