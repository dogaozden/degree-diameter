# Which elements stay uncovered in Haar graphs of odd diameter

Job beyond-d11, 2026-11-01. Director's lemma plus the hole counts of squad card r2/d04
(research/squads/beyond11/r2/d04/, haar_hole.c, *.cls.txt).

## Setting

H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S, e in S, |S| = Δ. Odd diameter D = 2h + 1. Right
multiplication by G is transitive on each side, so diameter <= D iff the same-side balls of radius 2h around (e,A) and
(e,B) are everything:

- X_A = (S^-1 S)^h, the products w = s_1^-1 s_2 s_3^-1 s_4 ... s_(2h-1)^-1 s_(2h) (words of length 2h from (e,A));
- X_B = (S S^-1)^h, the same from (e,B).

(e in S makes these sets nested in h, so "within 2h" equals "exactly a word of length 2h".) Both conditions are needed
for non-abelian G (r1/c14 gives a D6 example where one holds and the other fails).

## Lemma (exact)

1. X_A = X_A^-1: reversing and inverting a word of X_A gives a word of X_A. So the words reaching x are in bijection
   with the words reaching x^-1, and for an **involution** x (x = x^-1) the word set of x is closed under this
   reversal.
   The pairing is exact: the reversed-inverted word of (s_1, ..., s_2h) is (s_2h, ..., s_1) read with the same
   alternating pattern, and it is the same letter sequence only if s_(2h+1-i) = s_i for all i; then the two middle
   letters s_h^(+-1) s_(h+1)^(-+1) cancel, and so on outwards, so the word is e. Hence for an involution x != e the
   letter sequences reaching x come in disjoint pairs, and their number is even.
2. For a **central** element c, the words reaching c are closed under rotation by two letters: if w = a b with
   a = s_1^-1 s_2, then b a = a^-1 (a b) a = c. The h rotations act on the word set of c.
3. For central c, c is in X_A iff c is in X_B: rotating s_1^-1 (s_2 ... s_2h) by one letter gives
   s_2 ... s_2h s_1^-1, a word of X_B, equal to a conjugate of c, so to c. A central hole is a hole on both sides.
4. If an automorphism alpha of order k maps S onto S, then alpha maps the words of x onto the words of alpha(x). For
   an alpha-fixed x it permutes the words of x, in orbits of size k when it acts freely on them (the orbit-search
   design, research/structured/STRUCTURE.md section 1).

## Heuristic consequence

If the number of words reaching a given element is roughly Poisson with mean lambda = W/N, but the words come in
clumps of c (an exact symmetry of the word set, acting freely), then the element is uncovered with probability about
exp(-lambda/c) instead of exp(-lambda). At the D = 11 cells lambda is 18-21 and h = 5:

| element type | clump size c | miss probability (lambda = 19) |
|---|---|---|
| generic | 1 | 5.6e-9 |
| involution | 2 | 7.5e-5 |
| alpha-fixed (k = 3) | 3 | 1.8e-3 |
| central | h = 5 | 2.2e-2 |
| central involution, alpha-fixed (-I in SL, k = 3) | up to 2 h k = 30 | up to 0.5 |

Counts in the two families (n odd, r of order 3 mod n without fixed points):

| G | involutions | central | alpha-fixed |
|---|---|---|---|
| SL(2,p) x Z_n | 1 (-I) | 2n ((+-I, z)) | about p (torus, z = 0) |
| PSL(2,p) x Z_n | about p^2/2 | n ((I, z)) | about p/2 |

So at odd D: PSL pays about (p^2/2) exp(-lambda/2) involution holes per side (10-15 at p ~ 550), SL pays only for -I,
2n central elements and about p torus elements. The best shape is **SL(2,p) x Z_n with n small (1-19) and p large**.
At even D, words reaching the other side have odd length, reversal changes the side and rotation changes the side, so
neither effect exists (D = 10, 12 values with PSL and n = 1 solved at once).

## Measurements (r2/d04, (11,11), ORBIT "3 3 2", three random symmetric S per group, holes of both sides)

| group | mu | total holes (3 seeds) | involutions | central | alpha-fixed |
|---|---|---|---|---|---|
| PSL(2,1063) x Z1 | 5.54 | 171, 136, 119 | 159, 132, 117 | 0 | 0-4 |
| PSL(2,557) x Z7 | 6.36 | 39, 59, 35 | 39, 53, 33 | 0 | 0-2 |
| PSL(2,151) x Z349 | 5.58 | 48, 24, 15 | 6, 6, 3 | 24, 12, 0 | 0 |
| SL(2,149) x Z181 | 5.22 | 60, 32, 66 | 0-6 | 24, 26, 24 | 0-6 |
| SL(2,251) x Z37 | 3.31 | 2, 10, 22 | 0-14 | 2, 2, 0 | 0-4 |

d04's fitted rates: involutions about 1.2e-4 per element per side (exp(-lambda/2) = 9.6e-5 at lambda = 18.5); central
elements 0.02-0.034 (exp(-lambda/5) = 0.025). The near misses of round 1 fit too: SL(2,193) x Z211 at (12,11) stalled
with -I as its only hole on both sides (item 3), SL(2,443) x Z7 at (11,11) with two torus elements.

Round-1 data agree: PSL n = 1 was the worst shape at (11,11) (c16, median 151) and at (13,9) (c11, c08, 87-111), and
n/p >= 40 was bad (central elements). This is why the job's D = 11 values use SL(2,p) x Z_n.

## Quantitative fit (round 3, card e14) and the even-D control (card e13)

- e14 (research/squads/beyond11/r3/e14/FIT.md): RANDORB medians for 22 SL/PSL groups at (11,9) (h = 4), n = 1..367,
  against expected holes = mu + I exp(-lambda/2) + C exp(-lambda/h) + F exp(-lambda/3) (generic term mu: the cost counts
  elements, so alpha only clumps them; it does not reduce their expected number). The model is 1.3-1.5x low at mu ~10 and
  2-2.3x low at mu 30-36; the involution term fits at about 1.3 exp(-lambda/2), the central term at about 2 exp(-lambda/4),
  worst for SL with n ~ 350. Random S have heavy tails (some samples cost 1e3-1e6), so medians were used.
- e13 (research/squads/beyond11/r3/e13/ANATOMY.md), (8,12), 62 random S: at even D there are no involution or rotation
  clumps, as predicted (and side B is always complete). Alpha-fixed holes are enriched, but most holes are ordinary
  elements; smaller p did not give fewer holes (median 14.5 for SL(2,271) x Z7, 19.5 for PSL(2,653), 57-62 for PSL(2,79-97)
  with large n). Every random S containing a generator of projective order 2 cost above 1e4.
- In practice even D was easy at these sizes: (11,12) solved at mu 8.7 in 85 evaluations and at mu 13.3 in 17
  (PSL(2,223) x Z1009), while the odd-D cells stall near mu 7-10.

## Near misses of the director's pushes (examples)

- (12,11) SL(2,193) x Z211, f = 0, mu 10.3: cost 2 = -I on both sides (item 3; n = 211 gives 422 central elements).
- (11,11) SL(2,443) x Z7, mu 7.2: cost 2 = two torus elements a I + b g (alpha-fixed).
- (11,11) SL(2,853) x Z1, mu 10.4: cost 2 = mat(406,240,613,646) and its inverse mat(646,613,240,406), both in the
  torus of g and on side A (items 1 and 4: an inverse pair of alpha-fixed elements; with n = 1 the torus, about p = 853
  elements, is the main special term: 853 exp(-lambda/3) ~ 2 at lambda = 17.9).
Balancing the torus term (~p exp(-lambda/3)) against the central term (~2n exp(-lambda/h)) at N = p^3 n fixed gives
n ~ 7-13 at the D = 11 cells, which is where the solved (11,11), (13,11), (14,11) groups sit (n = 19, 19, 7).
