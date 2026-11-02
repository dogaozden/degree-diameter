# a14 NOTE: single free orbit of an order-7 automorphism, and an abelian-quotient bottleneck

Tried: S = one free orbit {alpha^i x0, i = 0..6} (Delta = 7, no e) under alpha(M,z) = (g M g^-1, u z) on
G = SL(2,8) x Z_p, g = diag(t, t^-1) of order 7, u of order 7 mod p (p = 1 mod 7). Fix(alpha) = 7 elements.
G has order 504p; p = 59417 gives |G| = 29,946,168 (2|G| = 59,892,336, would beat 59,838,504).
Code: orb7.c (bitset BFS, left multiplication; cost = unvisited B within 11 steps). check_small.py is an independent
Python BFS on the explicit Haar graph; it matches orb7 level by level at p = 29 and p = 1009 (orbit and random S).

Measured at p = 59417 (|G| = 29.9M): orbit S holes at level 11: 10.9M to 29.9M (min 10.87M over 4 samples).
Baseline, 7 free random elements on the same group (RANDS=1): 13.1M to 17.9M holes. The size law predicts ~15.

Explanation (verified numerically):
- Walk words of length L in the Haar graph have exponent vector c in Z^7 (c_i = #uses of s_i in odd positions minus
  even positions), so the Z_p coordinate of the reached vertex is sum c_i z_i. For L = 11, sum c_i = 1 and |c|_1 <= 11.
  The number of such c is C_11 = 65,226 (C_9 = 22,645, C_7 = 6,328; enumerated).
- An orbit sample reached exactly 22,645 B-vertices at level 9 and 65,226 at level 11, i.e. the reach equals the number of
  exponent vectors: the orbit makes M a function of c (the group collapses to an abelian-like walk).
- For a random S the z-values reached are at most C_11 = 65k, while Z_p has 59,417 values: about exp(-1.1) = 1/3 of
  the z-values are missed, times 504 M-values, giving ~ 0.33 N holes (about 10M). That is the observed magnitude.
Consequence: any Haar graph whose group has an abelian quotient of order a needs a << C_11 ~ 6.5e4. Since z-part words
of length 11 have exponent sum 1, the abelian factor must be small. Here it is the whole Z_p factor, so the 504 p
family is dead at this size. (PSL(2,67) x Z199 has a = 199, far below C_11.)

Orbit structure: an order-7 automorphism that acts trivially on the abelian quotient gives all S elements the same
z-part z0, so every odd-level word has z = z0 (reach at most |H|): excluded. The automorphism must act on the abelian
quotient by a unit of order 7 (needs a prime n = 1 mod 7, e.g. 29), so G = H x Z_29 with |H| ~ 1.03M and an
order-7 automorphism with small fixed set. PSL(2,128) (order 2.1M, field automorphism of order 7, Fix = SL(2,2)) is
too big: with Z_29 it gives N = 60.8M, where the size law gives mu ~ 4.7e4. Not viable for D = 12.
Next: a different order-7 structure, or a different Delta with an orbit size dividing Delta, on a group whose abelian
quotient is small.

## Statistics added at the end of the round
- p = 59417 (|G| = 29.9M): 16 orbit samples, holes at level 11: min 10,868,907, mean 20.3M, max 29.9M.
  4 random-S samples (RANDS=1): min 12,025,819, mean 13.1M, max 14.1M. The orbit is not better than random S here.
- Smaller primes, random S, 6 samples each (holes at level 11, mean): p = 4019 (|G| = 2.03M): 33,683 (1.7 %);
  p = 9059 (|G| = 4.57M): 18,948. The crude model "504 p exp(-65226/p)" predicts 0 and 3,408 respectively, so the
  bottleneck count explains the orbit reach exactly (orbit runs hit C_9 = 22,645 and C_11 = 65,226 vertices), but
  it does not fully explain the residual holes of random S at small p. Those residuals are an open question.
- Verdict for this round: SL(2,8) x Z_p is a dead family for D = 12 at these sizes; single free orbits give no advantage.
