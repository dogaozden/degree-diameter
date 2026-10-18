# Diameter 5: our records are Haar graphs of metacyclic groups (d5-opus, 2026-10-18)

Transcribed by the main session from the agent's final reply.

## Structure
- None of the D = 5 records contain a GQ or projective plane; all have girth 6, no 4-cycles, every vertex has
  eccentricity 5.
- 2510 (Δ=9), 1140 (Δ=7), 352 (Δ=5): the automorphism group (pynauty) acts regularly on each side, so each is a Haar
  graph (one group orbit per side): Δ=9 the Frobenius group Z_251 ⋊ Z_5; Δ=7 Z_190 ⋊_11 Z_3 = (Z_19 ⋊ Z_3) × Z_10;
  Δ=5 a group of order 176. Eigenvalue multiplicities 10 and 6 match the 5- and 3-dimensional representations. The
  full automorphism group is just G.
- 162 and 354 are smaller lifts over a 3+3 base: 162 a Z_27-lift of K_{3,3} plus a doubled matching; 354 a Z_59-lift
  of K_{3,3} with two doubled matchings.
- Connection sets look random (e.g. Δ=9: S = {1, x^24y^4, x^27, x^32y, x^36y^3, x^139y^2, x^145y^4, x^243y, x^248y}).

## Lemma (proved)
Haar graph on G×{A,B}, edges (g,A)~(sg,B) for s ∈ S, |S| = Δ: diameter ≤ 5 iff (S⁻¹S)² = G and (SS⁻¹)² = G.
(Right multiplication is transitive on each side; vertices within distance 4 of (e,A) on side A are (S⁻¹S)², and
similarly for B; odd distances follow.) Counting words: |G| ≤ 1 + Δ(Δ−1) + Δ(Δ−1)³. In abelian groups many words
coincide, so good examples are non-abelian.

## Records
| cell | table | ours | group | file |
|---|---|---|---|---|
| (8,5) | 1710 | 1728 | Z_144 ⋊_25 Z_6 (Z_288 ⋊_97 Z_3 also works) | graphs/haar_d8_n1728.json |
| (9,5) | 2496 | 2530 (was 2510) | Z_115 ⋊_6 Z_11 | graphs/haar_d9_n2530.json |
S is stored in each JSON's "construction" field.

## Near misses (annealing over Z_m ⋊ Z_k)
| Δ | group order needed | orders tried | best |
|---|---|---|---|
| 6 | 343 (beats 684) | 343-362, all metacyclic | 2 elements uncovered |
| 8 | > 864 | 875-1080 | 4 uncovered at 882 |
| 9 | > 1265 | up to 1420 | 1-2 uncovered at 1260, 1280, 1287, 1310, 1378 |
| 10 | 2001 (beats 4000) | 2002-2040 | 6 uncovered (Z_401 ⋊ Z_5, 4 min) |
Records reach 0.52 (Δ=5), 0.37 (Δ=7), 0.31 (Δ=8), 0.27 (Δ=9) of the word bound; the table needs 0.27 at Δ=10 and 0.26
at Δ=11.

## Next
1. Faster search: incremental coverage updates (about 4Δ³ words change per move vs Δ⁴ recount), best-of-sample
   moves; long runs on near misses (Δ=9 at 1280-1310, Δ=10 at 2005/2016).
2. More groups: Z_p² ⋊ Z_k, products of Frobenius groups, arbitrary groups by multiplication table (smooth orders like
   864 = 2^5·3^3 were solved at once by two groups).
3. Lifts over bigger bases (2+2, 3+3), same reduced test (one BFS per base vertex).
4. Find the Δ ≥ 12 table values.

## Round 2 (haar-haiku, incremental search haar_search2.c, about 1.8x faster)
- (9,5): cost 0 at group orders 1266, 1280 and 1310; best 1310 = Z_131 ⋊_53 Z_10 gives a 9-regular diameter-5 graph on
  2620 vertices (graphs/haar_d9_n2620.json, passes verify_record.py; solution sols/h2_d9_N1310_m131_k10_l53.txt).
- Still short: Δ=6 best 2 uncovered (orders 351, 355); Δ=8 best 2 at 882; Δ=10 best 8 at 2005; Δ=9 at 1378 not solved.
