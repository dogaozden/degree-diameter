# Two small facts behind the beyond-d13 values

Job beyond-d13 (2026-11-01). Plain statements with proofs; the measurements are in the squad notes cited.

## 1. Odd-order groups have no special holes at odd diameter

Setting (research/frontier/beyond11/ODD_D_HOLES.md): Haar graph H(G,S), (g,A) ~ (s g, B), e in S, odd D = 2h + 1.
By vertex-transitivity on each side, diameter <= D iff X_A = (S^-1 S)^h = G and X_B = (S S^-1)^h = G (words of length
2h; e in S makes the balls nested). ODD_D_HOLES.md proves: (i) the words of X_A reaching x and x^-1 are in bijection
(reverse and invert), so for an involution the words pair up and it is missed with probability ~ e^(-λ/2) instead of
e^(-λ) (λ = W/N); (ii) the words reaching a central element are closed under rotation by two letters, so it is missed
with probability ~ e^(-λ/h), and on both sides at once.

**Fact 1.** If |G| is odd, (i) never applies (no involutions). If G = Z_m x|_r Z_k with m prime and r of order k > 1
modulo m (a Frobenius group of order m k), then Z(G) = 1, so (ii) applies only to e.

Proof. Odd order: an involution would have order 2, which divides |G|. Centre: (a,j)(b,l) = (a + r^j b, j + l) and
(b,l)(a,j) = (b + r^l a, j + l), so (a,j) is central iff a + r^j b = b + r^l a for all (b,l), i.e. (r^j - 1) b = (r^l - 1) a
for all b, l. Taking l = 0, b = 1: r^j = 1, so j = 0 (r has order k). Then (r^l - 1) a = 0 for all l; with l = 1,
r - 1 is a unit mod the prime m (r != 1), so a = 0. For a product of Frobenius groups the centre is the product of the
centres, again trivial. QED.

So in these groups every element is "generic" in the sense of ODD_D_HOLES.md, and the only obstruction left is the
generic one (and the growth obstruction below). Measured: at (4,13) the SL/PSL(2,p) x Z_n orbit searches stop at
170,520 (PSL(2,29) x Z7, exhaustive orbit scan), the Frobenius group Z4903 x|_230 Z19 gives 186,314; at (5,13)
3,217,056 (PSL(2,47) x Z31) against 3,525,298 for (Z29 x|_16 Z7) x (Z457 x|_289 Z19); at (4,11) 24,360 (PSL(2,29))
against 27,554 (Z599 x|_498 Z23). At even D, where neither clump exists for any group, metacyclic groups gave no gain
(squad r2/e06), as Fact 1 predicts.

**Growth caveat.** Z_m x|_r Z_k has the abelian normal subgroup Z_m of index k. The a-part of a word is
sum_i r^(J_i) a_i (J_i = partial sums of the Z_k parts), so it depends only on the multiset of pairs (J_i, letter_i):
for small k the group is "nearly abelian" and words collide. Measured word cover of the radius-12 ball at (4,13),
random S (squad r2/e11, ODD_ORDER.md): 1 % for k = 1, 6 % for k = 3, 73 % for k = 5, 91 % for k = 9, 97-99 % for
k >= 11. The values above all use k >= 7 per factor (k = 19, 23 for single groups).

## 2. An upper bound for cyclic lifts

Setting (squad r2/e16, lift.c): a base graph B (bipartite, regular), voltages x_e in Z_n on its edges, the lift has
vertices (v, g), v in B, g in Z_n, edges (u, g) ~ (w, g + x_e) for e = (u,w). Rotation g -> g + c is an automorphism, so
diameter <= D iff every (v, g) is within D of (s, 0) for every base vertex s.

**Fact 2.** For base vertices s, v let W(s, v, D) be the number of distinct net traversal vectors (the vector in Z^E of
signed edge counts) of walks s -> v of length <= D in B. If the Z_n lift has diameter <= D then n <= W(s, v, D) for all
s, v; so n b <= b min_{s,v} W(s, v, D).

Proof. The lift of a walk from (s, 0) ends at (v, sum_e c_e x_e) where c is its net traversal vector; so the endpoints
over v reachable within D are at most the number of distinct c, W(s, v, D), and all n of them must be reached. QED.

(Nonbacktracking walks suffice for the count, since a backtrack does not change c and shortens nothing; parity: in a
bipartite base only walks of the right parity reach v.) Squad card r3/f03 (LIFTS.md) computed the walk counts: for
GP(10,3) at D = 13, 20,258 distinct classes among 24,574 nonbacktracking walks (min over endpoints 647), at D = 14
36,404 (min 1,197); for K4,4 at D = 13 the classes are 9 % of the walks, which caps K4,4 lifts near 31,000 vertices
by the random-voltage model (Fact 2's hard bound is 8 x 25,116 = 200,928). Found: GP(10,3) x Z160 (3,200) at D = 13 and
x Z280 (5,600) at D = 14; Fact 2 allows n <= 647 and <= 1,197. Card r4/g11 tabulates the bound for more bases.
