# i12: first-moment count, random S vs orbit S (job beyond-d13, round 6)

Notation: N = |G| (vertices = 2N), d = Delta, D odd (13). cost = A-side + B-side uncovered (haar_big0 header), so one
side has about cost/2 holes. mu = N exp(-W/N), W = free word count (pick.py). Code: fm.py, table.py in this folder.

## 1. Candidate counts (ln #S)
- Random S = {e} + (d-1) free elements: C_rand = N^(d-1)/(d-1)!. Delta=4: ln C = 32.8, 39.7, 43.0, 46.6 at N = 1e5, 1e6, 3e6, 1e7.
- Orbit S, ORBIT "3 m f" (m orbits of size 3, f in {0,1,2}, e counted when f >= 1): C_orb ~ (N/3)^m |Fix|^(f-1) / m!.
  Delta=4 ("3 1 1"): ln C = 10.4, 12.7, 13.8, 15.0 at the same N. Delta=6 ("3 2 0", N = 2.1e7): ln C = 30.8 vs 79.5 random.
- The random form has 22 nats (Delta=4, N = 1e5) to 49 nats (Delta=6, N = 2e7) more candidates. Divided by the
  independent-event model P0 = exp(-mu), this is the whole first-moment argument: E = C P0.

## 2. The Poisson model with the size-law mu is far too optimistic
- Size-law mu is the mean hole count of random S. Measured medians are much larger (one side, cost/2):
  sl37 x Z397 (N 2.0e7, mu 5.1): random median cost 254 (about 127 per side); mu is 25 times smaller.
  sl113 x 1 (N 1.4e6, mu 0.27): random median 36 (about 18 per side); 67 times.
  psl67 x Z13 (N 2.0e6, mu 20.9): median 112,047; the gap is 2,700 times.
  So E = C exp(-mu) overstates the existence of solutions by orders of magnitude; the lower tail, not the mean, decides.
- Lower tail (what the first moment needs): Delta=5 random has zero-cost S: sl113 x 1 (0 of 300 samples at min 0; p10 = 4),
  psl47 x Z31 (min 0 of 300), sl37 x Z31 (min 0), sl61 x Z7 (min 0). So P0 is at least about 1/300 at N = 1.4-1.6e6, i.e.
  an effective mu' near 5.7, against mu = 0.3-1.5 there. With ln C = 52 at N = 1.4e6 (d = 5), existence is never the limit.
- At Delta = 4 and 5 the random form is limited by search and by the decay of P0 with N, not by the count.

## 3. Orbit vs random on the same group (the direct comparison)
| group (N) | form | min | median | 10 samples or 300 |
|---|---|---|---|---|
| sl37 x Z397 (2.0e7, mu 5.1, d=6) | random | 202 | 254 | 10 |
| sl37 x Z397 | orbit 3 2 0 (Fix 35) | 198 | 1266 | 10 |
| meta 1079011x19 (2.05e7, mu 7.0, d=6) | random | 100 | 260 | 10 |
| meta 1079011x19 | orbit 3 2 0 (Fix 18) | 1.65e7 | 1.69e7 | 10 |
- The best orbit S reaches the same floor (about 200) as random S on sl37, but its typical S is 5 times worse.
  The floor is common to both forms: SL(2,37) x Z397 has 2n = 794 central elements; ODD_D_HOLES gives a miss
  probability exp(-lambda/h) = exp(-15.19/6) = 0.080 each, so about 63 misses per side, about 126 in cost. This is the
  same order as the observed floor (198-202). Central elements, not the orbit form, set the floor for SL x Z_n at odd D.
- On the metacyclic group the orbit form is broken: median 80 percent of G uncovered. Hypothesis (not checked):
  alpha acts as a scaling on the normal Z_p, so the orbit elements generate a proper subgroup. Check <S S^-1> = G first.

## 4. Where each form stopped (records, D = 13)
- Random S, Delta=4: metacyclic group, N = 9.3e4, mu 17.9, value 186,314.
- Random S, Delta=5: N = 1.8e6 (product of Frobenius groups), mu 5.4.
- Orbit S, Delta=6..9: N = 2.1e7 - 3.8e9, mu 9.3, 8.5, 7.5, 3.1. The orbit records are at small mu (the holes are
  correlated) and the first moment is far from the limit (ln C - mu about 22-58 nats), so the limit is structural.
- Reading: for both forms the per-N limit is set by the hole distribution (its lower tail), which the size law does not
  capture. The first-moment count only says that random S always has candidates to spare.

## 5. Rule for the next round
Use the lower tail, not mu. Run RANDORB (300 samples) on each candidate group at Delta = 4, 5: hit rate p = (#cost 0)/300.
Continue to larger N while p >= 1/3000 (RANDORB took 57 s for 300 samples at N = 1.4e6, about 0.2 s each). For Delta >= 6, screen PSL (no centre) with
orbit S, and drop SL x Z_n at odd D (central floor). Verify <S S^-1> = G before any orbit run on a metacyclic group.
