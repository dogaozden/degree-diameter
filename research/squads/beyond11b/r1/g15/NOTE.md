# g15 (wildcard C): word-count facts for odd-D Haar graphs H(G,S), with checks

Job beyond-d11b, round 1, card g15. Scope: exact statements about the words that reach an element at D = 2h+1, for
G = SL(2,p) x Z_n with an automorphism alpha of order 3 and f = 0 (no alpha-fixed generator in S). Checks are on
SL(2,5) x Z_7 (alpha = conjugation by M = [[0,-1],[1,-1]], order 3, times z -> 2z), so they are small-case
computations; the proofs do not use the group.

## Notation

Pair sequences: q = ((s_1,t_1), ..., (s_h,t_h)) in (S x S)^h. Block a_i = s_i^-1 t_i, product P(q) = a_1 a_2 ... a_h.
Let n_h(x) = #{q : P(q) = x}. Then (e,A) reaches (x,A) by a walk of length 2h exactly when n_h(x) > 0, i.e.
x in W_h = (S^-1 S)^h. Since e is in S, W_h is nested in h, so "within 2h" is "n_h(x) > 0 for some h' <= h".
Same-side sets for (e,B): W'_h = (S S^-1)^h, with block s t^-1 (same proofs).

## Theorem 1 (invariance; exact)

Let alpha be an automorphism with alpha(S) = S, and iota the inversion. Then for every x in G
  n_h(alpha(x)) = n_h(x)   and   n_h(x^-1) = n_h(x).

Proof. (i) (s_i,t_i) -> (alpha s_i, alpha t_i) is a bijection of pair sequences over S; alpha(a_i) = alpha(s_i)^-1 alpha(t_i)
and alpha(P) = alpha(x). (ii) The reversal R: (s_1,t_1),...,(s_h,t_h) -> (t_h,s_h),...,(t_1,s_1) is a bijection, and its
blocks are a'_i = a_(h+1-i)^-1 (since (t,s) gives t^-1 s = (s^-1 t)^-1). So P(R q) = (a_h^-1 ... a_1^-1) = P(q)^-1.
Hence the distances from (e,A) to (x,A), (alpha x, A), (x^-1, A) coincide. The same holds for W'_h with the block s t^-1.
Consequence: H = <alpha, iota> (order 6, alpha and iota commute) acts on G, and the uncovered set at D = 2h+1 on each side
is a union of H-orbits. A search over alpha-invariant S needs one coverage test per H-orbit (up to 6x fewer tests).

## Theorem 2 (parity of word counts; exact)

(a) Reversal-fixed sequences (R q = q, i.e. (s_i,t_i) = (t_(h+1-i), s_(h+1-i))) satisfy a_(h+1-i) = a_i^-1, with the middle
block (h odd) equal to e. Pairing the factors gives P(q) = e. So R has no fixed point among sequences with product x != e.
For an involution x (x = x^-1), R maps the x-set to itself with no fixed point, so n_h(x) is even.

(b) If f = 0, alpha has no fixed point on S, so alpha acts freely on pair sequences. For an alpha-fixed x the x-set is
alpha-invariant, so n_h(x) = 0 mod 3.

(c) For central x (x = -I in SL(2,p)): rotation of the blocks, (a_1,...,a_h) -> (a_2,...,a_h,a_1), keeps the product
(a_1^-1 x a_1 = x), so Z_h acts on the x-set. With (a) and (b) the group D_h x Z_3 (order 6h) acts on the -I set, and
  n_h(-I) = 0 mod 6 for every S with f = 0 and every h.
Remark: (b) needs f = 0. With f >= 1 the alpha-fixed sequences form the extra clumps listed in ODD_D_HOLES.md.

## Proposition 3 (central pairs give free coverage; exact sufficient condition)

Let C(S) = Z(G) cap (S^-1 S). If s,u in S and c = s^-1 u is central, then t = s c gives s t^-1 = c^-1 and t s^-1 = c, so
c is a block of length 1, c in W_1 and c in W'_1. Hence every element of C(S) is covered on both sides at every odd
D >= 3, and at every even D >= 2 on side A. Test cost: O(Delta^2) products. Verified by BFS (check3.py): in 400 random
alpha-invariant S the distances from (e,A) and (e,B) to every c in C(S) are <= 2 (0 violations).

## Proposition 4 (buying -I with a pair is a bad trade; numerical)

-I is in S^-1 S iff S contains some s and -s (blocks s^-1(-s) = -I). Then the projection to PSL(2,p) x Z_n has each
element twice, so the effective degree halves. Measured on SL(2,5) x Z_7, Delta = 9, D = 5 (check5.py, check6.py):
- random alpha-invariant S: diameter <= 5 in 9/60 trials (check5); mean uncovered elements on side A 36.6 over 40 trials (check6);
- S forced to contain s, -s (orbit of s and of -s, plus one random orbit): diameter <= 5 in 0/60 (check5); mean uncovered 281.2 over 40 trials (check6).
So do not spend a pair on -I; Proposition 3 (a free central block) only helps when the pair arises by chance.

## Exponent for the -I hole (heuristic, measured; NOT a theorem)

If word-orbits land on -I uniformly, the number of D_h x Z_3 orbits hitting -I is Poisson with mean lambda/c, lambda =
Delta^(2h)/N and c = average orbit size (6h generically). Then P(-I uncovered on side A) ~ exp(-lambda/(6h)). Measured:
- h = 2, Delta = 9, N = 840 (lambda = 7.81), 150 random S (check.py 2 3 150 7): 0.447 observed, exp(-lambda/12) = 0.522;
- h = 3, Delta = 6, N = 840 (lambda = 55.5), 150 random S (check.py 3 2 150 13): 0.093 observed, exp(-lambda/18) = 0.046;
  among S whose graph is connected: 0.109 (check4.py).
So the Poisson-orbit form is about right at h = 2 but underestimates by about 2x at h = 3. The spread over S (counts from 0
to 486 at h = 3) is overdispersed, so the exponent is only a guide. Do not use exp(-lambda/6h) for sharp predictions.

## Checks (all in this folder; BFS = all-pairs distances of the Haar graph, the ground truth)

- check.py: BFS from (e,A) and (e,B). Side-A distances are invariant under alpha and inversion: 0 violations at h = 2
  (20 and 150 S) and h = 3 (150 S). Count n_h(-I) is 0 mod 6 in all trials (h = 2 and 3).
- check2.py: explicit enumeration of pair sequences (h = 2, Delta = 6 and 9; 14 S). The -I set is closed under rotation,
  reversal and alpha in every trial; counts seen 6, 12, 18 (orbit sizes 6 and 12 = 6h); count minus reversal-fixed
  count is even in every trial.
- check3.py: Proposition 3 (0 violations); check4.py: connectivity split; check5.py and check6.py: Proposition 4.

## Status

Theorems 1, 2 and Proposition 3 are proved and match the computations. Proposition 4 and the exponent are numerical
observations on one small group. No record: this card did not build a graph. The director can use Theorem 1 (one
coverage test per H-orbit, H of order 6) and Theorem 2(c) (n_h(-I) divisible by 6 under f = 0, so -I hole counts
come in blocks of 6) as stated; Proposition 4 says to avoid buying -I with a pair.

## Extra checks (check7.py)

- Side B: distances from (e,B) are invariant under alpha and inversion (Theorem 1 for W'_h): 0 violations over 60 S.
- h = 3, Delta = 6, explicit enumeration of pair sequences with product -I (4 S): the set is closed under rotation,
  reversal and alpha in all 4 trials, and its size is 0 mod 6 (counts 12, 0, 18, 12).
