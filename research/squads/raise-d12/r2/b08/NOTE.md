b08 NOTE: the two walls of round 1 as lemmas with counts (raise-d12 round 2). Code: code/abel.py, scan.py,
enum_fast.py (abelian coverage), code/moore.py, moore_cov.py (H(2) base). All tables below are computed by that code.
Score 0 by design; this is a theory deliverable.

=== Part 1. Abelian-quotient wall (Haar graphs H(G,S), D = 12) ===

Setting. G with abelianization A = G/[G,G] = Z_n (SL/PSL(2,q) perfect). S = {e} + F + O, where F are f-1
alpha-fixed letters (z = 0 when gcd(r-1,n)=1), and O is one alpha-orbit of size k with z-values w_i = r^i z0
(z0 a unit, r of order k mod n, k prime).

Lemma 1 (signed counts). A B-vertex g lies within distance 11 of (e,A) only if g = s1 s2^-1 s3 ... s_L (L odd, L <= 11)
for some letters. Its image in A is sum_s c_s phi(s), where c_s = #(odd positions with s) - #(even positions with s),
so sum c_s = 1 and ||c||_1 <= L <= 11. Conversely every such c is realized by a word of length ||c||_1 (put the
positive letters at odd positions, the negative ones at even positions). So the reachable image set is
R(S) = { sum_s c_s phi(s) : c in Z^S, sum c_s = 1, ||c||_1 <= 11 }.

Lemma 2 (reduction). The letters e and F have phi = 0, so they only absorb the leftover sum. Using one zero letter
to absorb t = 1 - sum u_i costs |t|. Hence
  R(S) = { sum_i u_i w_i mod n : u in Z^k, ||u||_1 + |1 - sum u_i| <= 11 }.
The support of R does NOT depend on f (only the multiplicity does). It depends only on k, r and n (z0 scales).
Multiplicity: cov(x) = #{c in Z^Delta : ... = x}, the number of signed-count patterns hitting x. N_c = total count.

Lemma 3 (cost of a missing class). If x is not in R(S), then every element of the coset phi^-1(x) (size |G|/n =
|[G,G]|) is unreached at level 11, so holes >= (n - |R|) * |G|/n. The wall is all-or-nothing: a missing residue costs
|[G,G]| holes (504 for SL(2,8) x Z_n, 32,736 for SL(2,32) x Z_n).

Lemma 4 (k = 3 saturation). For r of order 3, 1 + r + r^2 = 0 mod prime n, so the residues are a + b r with (a,b) in a
2-dimensional lattice projection. R saturates at a fixed number of values (about 289) for large n.

Table A (scan.py; prime n = 1 mod k; "full" = largest prime n with R = n, f-independent;
"min>=20" = largest prime n found with min over residues of cov >= 20 for the given f; Delta = k + f):
  k=3: full n = 241 (all f). min>=20: Delta 4: 31; Delta 5: 127; Delta 6: 163; Delta 7: 163 (min 51).
       N_c = 724, 3855, 17088, 65226.  Large n: R(1063) = 289.
  k=5: full n = 7691 (all f; r = 6179). min>=20: Delta 6: 661; Delta 7: 2141; Delta 8: 3821;
       Delta 9: none found in [6011, 33364] (scan timed out, unresolved); Delta 10: none found in [64231, 92.6k]
       (scan timed out, unresolved). N_c = 17088, 65226, 219864, 667287, 1851580.
  k=7: NOT completed (795,455 lattice points; the full scan did not finish in the time box). Known point:
       n = 71, Delta = 8: R = 71 (full), min cov 3064.
  Round-1 rule "n < ~300 for k = 5, 7" was too strict for full coverage (k=5 full up to 7691), but at 20-fold
  coverage the k=5 ceiling is 661 to 3821 for Delta 6 to 8. Coverage is in signed-count patterns, not group elements,
  so the 20-fold criterion is a heuristic.

Round-1 checks (R = abelian image count; forced holes = (n - R)/n of the B-side at least):
  SL(2,8) x Z73, Delta 4, k=3: R = 73 (full), min cov 7, mean 9.9. The wall does NOT bind. The min-cost-61 state
          is not abelian; the obstruction is non-abelian.
  SL(2,8) x Z1063, Delta 5, k=3 (e + 1 fixed + 3-orbit): R = 289 (27.2%), so at least 72.8% of the B-side is forced
          unreached. Round 1 observed 82% uncovered (a10, RANDORB), which is consistent. a05's "199" is lower than the
          signed-count value 289, so a05 likely dropped negative counts.
  SL(2,8) x Z59417, k=3: R <= 289 (saturation), so >= 99.5% of the B-side is forced unreached. Dead.
  SL(2,32) x Z151, Delta 6, k=5: R = 151 (full), min cov 103. Not binding (director's min cost 15 is consistent).
  SL(2,32) x Z941, Delta 7, k=5 (assumed e + 1 fixed + 5-orbit): R = 941 (full), min cov 56. Not binding; the
          min-395 state is non-abelian.
  SL(2,128) x Z71, Delta 8, k=7: R = 71 (full), min cov 3064. Consistent with the (8,12) find.
  PSL(2,243) x Z271, Delta 10, k=5: R = 271 (full), min cov 5343. Consistent with the cost-1 state.
Conclusion: the abelian wall is a hard k=3 ceiling (n <= 241 full, and about 289 values at most), while for k=5
and 7 it is loose (full cover to 7691). Round-1 failures at (4..6,12) with k=3 or with Z_n of size 1000+ are the
wall. Failures with n <= 300 are not explained by the abelian level.

=== Part 2. Moore-base wall (H(2) = Tutte 12-cage base, cubic, 126 vertices, girth 12, diameter 6) ===

Count (moore.py, from the source point 0): non-backtracking walks of length <= 12 total 12,286 = 1 + 3(2^12-1).
Odd-length walks (<= 11) reaching the lines: 4095 = 3(1+4+16+64+256+1024), exactly 65 to EACH of the 63 lines (min = max = 65).
Walks to points (even length <= 12): 129 to 193 each, not equidistributed.
Distinct cotree voltage vectors: all 65 walks to each line are distinct, and their rank over Q is 64 of 65.
So they are nearly independent. The k=3 lattice collapse does NOT happen here.

Abelian coverage (moore_cov.py, random phi in Z_n^64, 300 trials): fraction of point-line pairs covered and the
independent model P(65 uniform balls cover n bins):
  n=6:  pair cover 1.0000 (model 1.0000)
  n=8:  0.9983 (0.9986)
  n=10: 0.9881 (0.9894)
  n=11: 0.9788 (0.9777)
  n=13: 0.9307 (0.9300)
  n=17: 0.7112 (0.7072)
So at the abelian level, the 65 walks behave like independent uniform voltages. The per-pair size law applies with
W = 65: mu(m) = m exp(-65/m) expected uncovered elements per pair.
  m: 6 (0.0001), 8 (0.0024), 10 (0.015), 11 (0.030), 12 (0.053), 13 (0.088), 16 (0.28), 19 (0.62), 21 (0.95),
     24 (1.60), 32 (4.2), 65 (23.9).
Exact necessary condition: each point-line pair needs all m elements covered by the 65 walks, so m <= 65 and
N = 126 m <= 8190 for any regular lift of this base. That matches M_b - 6 = 8184.

Why Moore bases are worse than small bases at equal N. For a bipartite cubic base with b vertices (b/2 per side),
the 4095 odd walks spread over b/2 targets, so W_b = 8190/b per target, and with m = N/b the ratio W/m = 8190/N is the
same for every base. The per-pair failure mu_pair = (N/b) exp(-8190/N) grows with N/b, but the number of target
pairs is about b^2/2, so the expected number of failing pairs is about (b N / 2) exp(-8190/N). At equal N, a Moore
base (b = 126) has about 21 times more failing pairs than a 6-vertex base (N = 2646: 7,550 vs 359 expected failing pairs
in the independent model). The Moore base is worse because of the number of pairs it must cover, not because its
walks are correlated.
Caveat: the independent model is pessimistic for full lifts. Round 1 found a valid m = 11 lift (1,386 vertices,
apsp-checked by a01), while the independent model predicts about 237 failing pairs at m = 11. The cross-pair
structure helps, and I did not explain why.

=== What is not done ===
k=7 full and min>=20 scans; k=5 min>=20 at Delta 9..11 (timed out); composite n; the z0-nonunit case; non-abelian
explanation of the Z73 min-61 state.
