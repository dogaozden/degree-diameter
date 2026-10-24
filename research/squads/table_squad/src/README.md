# haar_inv.c

A copy of research/structured/haar_sym.c (branch claude/structured-search-orbit-04hefm, commit 1c20eb4) with two
additions; everything else (groups, α choice, cost, checks, solution format) is unchanged.

- `INV=1` (with ORBIT="2 m f" or "2k0 m f", k0 odd): the orbit map becomes inversion ∘ α, an anti-automorphism, so S is
  closed under inverses (for k0 = 1) or is a union of blocks O ∪ O⁻¹ of an order-k0 conjugation orbit O.
- `EXHAUST=1` (with ORBIT): evaluates every S = {e} ∪ (f−1 fixed generators) ∪ (m distinct α-orbits), orbits taken by
  their smallest element. `EXSPLIT=a/b` keeps only combinations whose first orbit index is ≡ a mod b (to run b
  processes). `EXFIX=i` keeps only the i-th fixed-generator choice (useful when the choices are equivalent, e.g. t and t⁻¹: inverting
  S swaps the two sides of the Haar graph and preserves the total cost). `EXBOUND=B` (default and maximum 7) abandons a candidate once its cost is ≥ B. Prints every cost-0 S,
  writes the first one (checked by haar_sym's full diameter check, as in RANDORB), and ends with a line
  `EXHAUST ... evaluated=… zero=… min=… counts(0..6,>=7): …`.

Build: `gcc -O3 -march=native -fopenmp -o haar_inv haar_inv.c -lm`.
Validation: on (9,5) SL(2,11), ORBIT="3 3 0", EXSPLIT=0/40 evaluates 390,445 sets in 3.3 s and finds 3 of cost 0; the
written one is VALID by build_haar2.py and apsp.c.
