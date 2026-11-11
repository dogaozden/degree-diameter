# Referee report: OMEGA_REPAIR.md, Lemmas 4.1-4.4 and Theorem 4.5 (q = 7)

Branch claude/thm-omega-repair-m4luls at f350f66 (written by an independent agent session; copied here unchanged except for
this path note). Own scripts (not reusing degen.py/perpbound.py code), copied to this folder from
/tmp/claude-0/-home-user-degree-diameter/ca6226f2-6ede-597a-a68d-9b6299fc1069/scratchpad/ (mydegen.py, myperp.py,
myover.py, e2e.py). Overall: I could not break the q = 7 argument. Every step checks. The notes below are presentation points, not gaps.

## Lemma 4.1: correct
The Gram matrix [[0,a,b],[a,0,c],[b,c,0]] has determinant 2abc. Its rank is 3 if abc != 0, 2 if one or two entries are
nonzero, and 0 otherwise. Rank 1 is impossible because a rank-1 symmetric matrix lambda*v*v^T with zero diagonal is 0.
rad(Pi^perp) = Pi^perp ∩ Pi = rad(Pi), so its dimension is 0, 1 or 3. The counts are then Q+(3,q) (q+1)^2 or Q-(3,q)
q^2+1; a cone r*conic, 1+q(q+1); or Pi itself, q^2+q+1 (Q(w) != 0 on the complement, since Q(6,q) has no singular
4-space). Pair overlap: (q^3+q^2+q+1) - |<y,y',t>^perp ∩ Q| >= q^3 - q. "t not on yy'" fails only when t, y, y' lie on
one totally singular line (a hyperbolic line has just 2 singular points), so it is exactly "not aligned". I sampled
H(7) myself (6,000 triples, biased towards perpendicular ones). Pair overlaps in opp(t) were {336, 343, 350} =
{q^3-q, q^3, q^3+q}, and triple overlaps in Q were {50, 57, 64}. Both bounds are attained.

## Lemma 4.2: correct
If y_i = t, its ball misses opp(t); if y_i = y_j, the two balls are one. So |U C_i| <= 4q^4, and
16,807 - 9,604 - 6,860 = 343.

## Lemma 4.3: correct (independent enumeration agrees exactly)
The list of structures is exhaustive. Three collinear singular points span a totally singular line. So collinear
triples among the y_i are either inside an aligned class (overlap 0) or on a rich line. A rich line meets each aligned
class at most once, and two rich lines share at most one y. I enumerated all 353 labelled partial linear spaces on
{t, y1..y5} (blocks of size >= 3 meeting pairwise in <= 1 point). Blocks through t are aligned classes, the other
blocks are rich lines. This gives exactly the same 17 types, the same far-vertex bounds (from 662 down to -2058), the
same 8 forced types and the same forced-pair minima. No labelled instance has far <= 0 together with fewer than 6 forced
pairs. The minimum 6 is attained by (1,1,1,1,1) with one rich 4-line (far >= -426).

The Bonferroni terms are right. For a rich line with m points, all C(m,2) pair overlaps and C(m,3) triple overlaps
equal X = |l^perp ∩ opp(t)| >= q^3 - q. The net coefficient of X is -(C(m,2) - C(m,3)) = -2, -2, 0 for m = 3, 4, 5, so
using X >= q^3 - q is valid. For m = 5 the exact union 5q^4 - 4X is used instead. Triples containing an aligned pair
have overlap 0. Other triples are not collinear, so they are bounded by (q+1)^2.

degen.py keys types by (class sizes, rich-line sizes) and takes the minimum of far and of forced pairs separately.
This is conservative. degen_check.py never built types ((1,2,2),(3,3)) and ((1,1,1,2),(3,3)). That does not matter:
both are non-forced types, and only their forced-pair counts (12 and 9, pure combinatorics) are used.

## Lemma 4.4: correct
- Signs and normalisation: the identity #{Q = F = 0} = q^-2 Σ_{a,b} Σ_v ψ(...) is right. The b = 0 part is exactly
  q * q^6 = q^7. For b != 0, c = -a/b runs over F_q for each b, and |Σ_v ψ(b R_c)| = q^{7-r} q^{r/2} with r = 7 - d_c.
  Hence | |Perp| - (q^5-1)/(q-1) | <= Σ_c q^{1.5+d_c/2}, which is the affine count (A - 1)/(q - 1).
- Rank: the polar form of R_c is b(v, (h + h^-1 - c)w), and b is nondegenerate, so rank R_c = 7 - d_c (q odd).
- d_c <= 4 holds for non-semisimple h too:
  - (i) (h - μ) and (h - μ^-1) are coprime, so the kernel is the sum of true eigenspaces. A μ-eigenvector is singular,
    hence a fixed point.
  - (ii) An anisotropic eigenspace has dimension <= 2 (Chevalley-Warning), and dim ker N^2 <= 2 dim ker N.
  - (iii) The characteristic polynomial of h equals that of its semisimple part, which lies in a torus. The weights are
    0 and ±ε_i with Σε_i = 0. Multiplicity 3 for μ != ±1 needs μ^{±1±1±1} = 1, so μ^3 = 1, which puts μ in F_7.
- Σd_c <= 7 (distinct eigenvalues of h + h^-1). The integer vector (4,3,0,...) majorises every feasible one, so it
  maximises Σ q^{d_c/2}.
- At q = 7: 2801 + 907.49 + 343 + 92.60 = 4144.09, so the bound is 4,144.
- Unstated step: the collineation must be lifted to the det-1 matrix, which lies in G2(7) ≤ SO(7,7). Perp(-h) = Perp(h),
  so the choice of sign is harmless.
- Sampling: 10,452 random collineations (each checked line by line with Hex.perm, including powers), 5,763 of them
  fixed-point-free. |Perp| was always 2,752 or 2,850, max d_c = 4, Σd_c <= 6, and the per-element bound was never below
  |Perp| (smallest gap 111.1). Kernel patterns seen: (1), (2,1), (2,2,1), (2,2,2,1), (4,2,1).

## Theorem 4.5: correct
- The correspondence is right: {t, y_i} ↔ g_i and {y_i, y_j} ↔ g_i^-1 g_j, because g_i(t) ⊥ g_j(t) iff
  t ⊥ g_i^-1 g_j(t). So Σ_t #perp pairs = Σ_h |Perp(h)|. Numerically, with 5 random collineations: 42,015 = 42,015.
- Margin: 4 forced pairs would already suffice (4N = 78,432 > 62,160; 3N = 58,824 would not). Lemma 4.3 gives 6.
- Readings: every hub class meets two copies in every block, and inside a block one bar's classes link the five
  copies in a 5-cycle. So a class must have one colour in every copy, even if inner/outer colours were chosen per copy.
  Otherwise some transfer maps points to lines, which needs a duality, and H(7) has none (7 is not 3^e). That leaves
  reading 2 and its dual, which is now spelled out in the proof of Lemma 2.4.
- Geometric = twisted: holds by the same connectivity. The g_i lie in G2(7) because Aut H(7) = G2(7) for q prime.
- Starved pairs: I reran routes_dump on all 6 patterns. Every starved pair has R4 = 6 (5 twisted centres plus the
  identity), R0 = 0 and R2 <= 140, with max 140 in aaaab, aaabb, aabbb, abbbb and 104 in aaaaa, bbbbb. Both bars have
  starved pairs in every pattern. m2 counts distinct formal words, which bounds the number of distinct points for every t.
- Lemma 2.1 and Lemma 3.1 are used only as stated: the cover B(t,4) ∪ 5 radius-4 point balls ∪ m2 radius-2 point
  balls; |C_i| = q^4; at most q^2 per radius-2 ball; B(t,4) ∩ opp(t) = ∅. The dual reading uses the symmetric form
  (Lemma 2.4), and the route counts are independent of the reading.
- End-to-end run at q = 7 (e2e.py, 5 random g_i, all 19,608 t): max exact |U C_i| = 9,273 <= 9,285 (the
  general-position Bonferroni value).

Minor wording points (none affects validity):
- Lemma 4.4 should say which matrix lift is meant.
- "Convex in each d_c" would read better as "majorisation".
- Lemma 4.3 could note that rich lines are automatically totally singular.
