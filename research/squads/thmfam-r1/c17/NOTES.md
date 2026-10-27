# c17 notes (round thmfam-r1)

Family: S = O(X) u O(Y) in SL(2,q) x Z_m, Delta = 6, type 3+3. X = [[-2,-1],[1,0]], Y = [[0,-1],[1,1]]
(top two m=1 integer orbits from screen17.py on q = 29, 41; entries in [-2,2]).
Labels: mode E (alpha-equivariant): (x,z) -> (w x w^-1, r z), r a cube root of unity mod m. X gets z = 1, Y gets z = 2,
so the orbit labels are {1,r,r^2} and {2,2r,2r^2} (distinct for m in {19,31,37,43,61}).
m(q) = largest prime p <= q with p = 1 mod 3 (19,19,31,37,37,43,43,43,43,61 for q = 23..61).
Group: haar_ecc sl q m. Excess = diam - log_5(|G|), |G| = component size / 2 (same convention as family_score.py).

Files: gen17.py (family generator, modes E/N/Z), common17.py (helpers), screen17.py (m=1 pair screen),
run17.py (q loop), results.jsonl, run17.log.

Results (q = 23..61, 10 primes), mean excess:
- m = 1, same S (mode Z):                3.60
- random alpha-closed 3+3, m = 1, sl (5 seeds per q): 3.38
- E labels, m = m(q) (~q):               3.38   per-q paired diff vs m=1: mean -0.22, sd about 0.8 (not significant)
- N labels (dlog of first nonzero entry mod m, no symmetry): 6.70
Reason for N failure: the dlog labels of these integer matrices are degenerate (e.g. q=47, m=43: labels 23,23,13,23,23,0),
so the quotient Z_m graph has about 3 distinct generators and the diameter grows to 18-23 at q >= 47.
Best vs table: none (E family min diam 11 at q = 29, so no D <= 10 reached).
Caveat: the 2 fixed matrices were picked by screening at q = 29 and 41 (m = 1), so the m = 1 baseline is also tuned.
