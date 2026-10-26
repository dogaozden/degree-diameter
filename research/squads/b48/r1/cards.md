# Round 1 cards (48). Read HEADER.md first. Your folder: research/squads/b48/r1/<card>/

Shorthand: T = /home/user/degree-diameter/research/squads/b48/tools, B = the scratchpad bin dir in HEADER.md,
"Haar" = lift of the dipole (T/bases/dipole4.txt) = haar_fast's graphs, N = group order, n = vertices.
Scan data (metacyclic, order 1092..1120, 8 s each, haar_fast): r1/scan_meta_1092_1120.txt (lines "N m k r ord(r) :: RESULT ... best=cost").
Metacyclic notation: meta m k r = Z_m x|_r Z_k, needs r^k = 1 mod m.

## Metacyclic Haar graphs, structured slices (haar_fast)

**c01: break the cost-1 wall at order 1,100.** Z_55 x|_2 Z_20 sits at cost 1 (one element uncovered) after 25M evaluations on
two seeds. Find out which element stays uncovered and why: get a cost-1 S (run `$T/lift $T/bases/dipole4.txt meta:55:20:2 4 8 40 1 8 best.sol`;
it writes the best state), list the uncovered vertices with your own BFS, look at their Z_20 component, at the
subgroup they generate, at whether they are fixed by an automorphism, etc. If it is a structural obstruction, say what,
and pick the variant of the group (other r, other split 1,100 = m*k, non-faithful r) that avoids it; run it.

**c02: the k = 20 family at other orders.** meta m 20 r for m = 55..62 (N = 1,100..1,240) and every r with r^20 = 1 mod m
(also k = 10 and k = 40 with N in 1,094..1,240). Screen each with haar_fast 10 s, then 40 s on the best three, 2 seeds.

**c03: k in {6, 12, 24}** (the best k at order 1,092) at orders 1,094..1,200: enumerate the classes (r up to r -> r^j,
gcd(j,k) = 1), screen 8 s each with haar_fast, then 40 s runs on the best three.

**c04: k in {8, 16, 32} and k in {9, 18, 27, 36}** at orders 1,094..1,200, same protocol as c03.

**c05: prime k >= 5** (Frobenius-type Z_m x| Z_k, k prime, e.g. 5, 7, 11, 13) at orders 1,094..1,250, same protocol.

**c06: non-faithful actions.** meta m k r where ord(r) is a proper divisor of k (so Z_{k/ord(r)} is central-ish), orders
1,094..1,200, k in 4..60. Same protocol. Is non-faithful better or worse than faithful at equal order?

**c07: data-mine the scan.** Read r1/scan_meta_1092_1120.txt. Find a rule that predicts low cost from (m, k, r): ord(r),
gcd(r-1, m), number of a with r*a = a, k, the factorization of m, etc. Then use the rule to pick 10 untested groups with
N in 1,121..1,250, and test them (haar_fast, 15 s each). Report the rule in "idea" and the best result.

**c08: two-level design.** In Z_m x| Z_k the Z_k-parts of S = {e, x, y, z} decide which residue mod k each alternating
word (s1 s2^-1 s3 s4^-1 s5 s6^-1 s7) lands on. Choose the Z_k-parts first so that every residue mod k gets about
the same number of words of length <= 7 (both sides: words starting with s and with s^-1), then anneal only the
Z_m-parts with those fixed (write a small annealer; score with `$T/lift ... eval`). Test at N = 1,100 (meta 55 20 2,
meta 110 10 r) and N = 1,104..1,120.

## Symmetric generator sets

**c09: orbit sets S = {e, x, a(x), a^2(x)}** with a an automorphism of order 3 of the group (for metacyclic: scalings
(t, j) -> (u t, j) with u^3 = 1 mod m, conjugation by an element of order 3, or their product). Then S is fixed by a and
is decided by x alone: N candidates per (group, a). Score ALL x with `$T/lift $T/bases/dipole4.txt GROUP 4 8 eval`
(voltages in the dipole: the lift uses right multiplication; the voltage list "0 x a(x) a^2(x)" is fine since only the
graph matters). Because each (group, a) is cheap, scan many groups of order 1,094..1,400 (n up to 2,800).

**c10: other symmetric sets.** (i) a of order 4: S = {x, a(x), a^2(x), a^3(x)} (exhaustive over x). (ii) a of order 2:
S = {x, a(x), y, a(y)} (anneal y for the best x's). Groups: metacyclic and groups.py groups of order 1,094..1,300. Report
whether even-order symmetry hurts here (it creates word collisions at large degree; small degree is untested).

**c11: haar_sym orbit search.** `ORBIT="3 1 1"` (k = 3 orbit, one fixed generator e) with haar_sym on psl/sl/pgl(2,q)
x Z_n where every prime factor of n is 1 mod 3 (rule in research/structured/STRUCTURE.md §2), N in 1,094..1,400:
e.g. psl 7 x 7 (1,176), psl 5 x 19 (1,140), psl 5 x 21? (check n rule), sl 5 x 7? (840, too small), pgl 7 x 4?... List
all fitting (family, q, n) yourself. Screen with `RANDORB=2000` (cost statistics), then ORBIT runs of 40 s on the best.
Read research/structured/README.md for haar_sym's command line.

## Haar graphs of other groups

**c12: matrix x cyclic with haar_fast**: psl/sl/pgl(2,q) x Z_n with N in 1,094..1,300, e.g. psl 7 7 (1,176), psl 5 19
(1,140), sl 5 10 (1,200), pgl 5 10 (1,200), sl 3 46 (1,104), psl 9 3? (1,080, too small), pgl 7 4 (1,344). List all,
screen 10 s, then 40 s on the best three.

**c13: affine groups AGL(1,q) x Z_n with haar_fast** (`agl1 q` then n): agl1 11 10 (1,100), agl1 5 55 (1,100), agl1 7 27
(1,134), agl1 8 20 (1,120), agl1 9 16 (1,152), agl1 16 5 (1,200), agl1 4 92 (1,104), agl1 3 183 (1,098), agl1 13 7 (1,092,
control: 2,184). Screen 10 s, then 40 s on the best three.

**c14: Z_p^2 x| Z_k** (`semi p k a b c d` in groups.py, then lift with the dipole): orders 1,094..1,250, e.g. Z_7^2 x| Z_24
(1,176; Singer-type matrix of order 24 or 48/2), Z_13^2 x| Z_7 (1,183), Z_11^2 x| Z_10 (1,210, diagonal diag(u, v)
with different v), Z_5^2 x| Z_k with a matrix whose order divides k. Try irreducible (Singer) vs diagonal matrices.
Anneal 30 s each with lift.

**c15: direct products of two non-abelian groups** (groups.py "A x B", or haar_fast `prod G1 G2 n` where it applies):
S3 x meta(~183..200), A4 (agl1 4) x meta(~92..100), D5 x ..., SL(2,3) x dih 23 (1,104), S3 x S3 x meta(~31), Q8-type
(meta 4 2 3) x ..., total order 1,094..1,250. Anneal 30 s each.

**c16: smooth orders 1,152 and 1,200 (n = 2,304, 2,400).** These orders have very many groups. Build at least 8
non-isomorphic ones each: e.g. GL(2,3) x SL(2,3) (perm or matrices), S4 x S4 x Z2, SL(2,3) x SL(2,3) x Z2,
AGL(1,9) x Z16, (Z3^2 x| Q8) x Z16, SL(2,5) x Z10, A5 x Z20, S5 x Z10, Z5^2 x| Z48, AGL(1,25) x Z2 ... and anneal Haar
graphs (lift or haar_fast where it has the family). A success here would be a big jump.

**c17: permutation groups.** Wreath products (Z24 wr Z2 = 1,152, S3 wr Z2 x ..., etc.), imprimitive groups, and groups
generated by two random permutations of degree 6..14 whose order happens to lie in 1,094..1,300 (screen many random
pairs, keep those in range, check they are not abelian). Anneal Haar graphs on the best few (lift + groups.py perm).

## Lifts of bases with more than 2 vertices (n = b * N)

**c18: 2+2 bases** ($T/bases/b22_t1.txt, b22_t2.txt) with metacyclic groups of order 547..600 (n = 2,188..2,400): enumerate
classes with k in {4, 6, 8, 10, 12, 20, 24}, screen with lift 10 s, then 40 s on the best three.

**c19: 2+2 bases with non-metacyclic groups** of order 547..620: SL(2,5) x Z5 (600), A5 x Z10, S5 x Z5, Z5^2 x| Z24
(semi 5 24 ...), S4 x Z23 (552), SL(2,3) x Z23, A4 x Z46, agl1 11 x cyc 5 (550), agl1 5 x cyc 28 (560), psl2 7 x ...?
Anneal 30 s each.

**c20: 3+3 bases.** Enumerate all connected 4-regular bipartite multigraphs on 3+3 vertices (3x3 matrices with entries
>= 0, rows and columns summing to 4, up to row/column permutations; $T/bases/k33_matching.txt is one). Groups of
order 365..420 (n = 2,190..2,520): metacyclic, A5 x Z7 (420), SL(2,3) x Z16 (384), S4 x Z16, Z7^2 x| Z8 (392)... Find
which base works best, then push the order up.

**c21: 4+4 bases with non-abelian groups** of order 274..320: K_{4,4} ($T/bases/k44.txt) and other 4-regular bipartite
multigraphs on 4+4 vertices (cube Q3 plus the antipodal matching, C8 with alternate double edges, ...); groups:
metacyclic, S4 x Z12 (288), SL(2,3) x Z12, A4 x Z24, Z7^2 x| Z6 (294), A5 x Z5 (300), agl1 17 x cyc 2? (544, too big)...

**c22: abelian lifts, Exoo/Loz style.** Cyclic voltages Z_n on bases with b = 8..64 vertices (bigger bases have more
independent cycles, which abelian lifts need): K_{4,4} with n >= 274, random simple 4-regular bipartite bases on
6+6, 8+8, 10+10, 16+16 vertices, bipartite circulant-like bases. Find where cyclic lifts get closest at n >= 2,186.

**c23: lifts of PG(2,3)'s incidence graph** (13 points, 13 lines, 26 vertices, girth 6: the (4,3) Moore graph; build
it yourself) by groups of order 85..100: Z85 (n = 2,210), meta 29 3 r (87), meta 31 3 r (93), order-96 groups
(SL(2,3) x Z4, GL(2,3) x Z2, ...), meta 25 4 7 (100), Z5^2 x| Z4. Anneal 30 s each; push N up if close.

**c24: lifts of the GQ(3,3) incidence graph** (W(3): 40 points, 40 lines, 80 vertices, girth 8: the (4,4) Moore graph;
build it from the symplectic form on GF(3)^4) by groups of order 28..32 (n = 2,240..2,560): Z28, dih 14, meta 7 4 6,
Z29, Z30, dih 15, Z31, order-32 groups (meta 16 2 7, meta 8 4 3, meta 16 2 9, ...).

**c25: lifts of other girth-6 and girth-8 4-regular bipartite graphs with 30..80 vertices**: the biaffine plane
(AG(2,4) minus one parallel class, 16+16), Levi graphs of cyclic (v_4) configurations (lines {i, i+a, i+b, i+c} mod v
from Golomb rulers, v = 13..40), etc., by groups of order ceil(2,186/b)..2*that.

**c26: lifts of small-diameter graphs by small groups.** Our (4,5) record graph (162 vertices,
records/bipartite_dd/d4D5/162-c-d4d5-g002-c08.edges.txt) and other 4-regular bipartite graphs with 100..600 vertices and
diameter 5..7 (make some with haar_fast at D = 5, 6, 7, e.g. `haar_fast 4 6 ...` on groups of order 50..300), lifted by
groups of order 4..22 so that n >= 2,186 (162 x 14 = 2,268 with Z14 or dih 7, ...). Convert the graph to a lift base file.

**c27: big base, tiny group.** 4-regular bipartite graphs with 547..1,093 vertices and diameter <= 7 (e.g. Haar graphs
from haar_fast at D = 7 on groups of order 274..547) lifted by Z2, Z3, Z4 or Z2^2 (n = 2,188+). lift supports bases up
to 8,192 vertices. A 2-lift of a diameter-7 graph on 1,094 vertices needs, for every pair, walks of length <= 8 with both
voltages.

## Cayley graphs (vertex-transitive)

**c28: bipartite Cayley graphs Cay(G, {a, a^-1, b, b^-1})** of metacyclic G = Z_m x| Z_k with k even (parity = j mod 2),
|G| in 2,186..2,400, a and b with odd j. Base $T/bases/bouquet_2loops.txt; lift penalises non-bipartite lifts, but it
is better to only allow odd-j voltages: write a small annealer that calls `lift ... eval`, or patch a copy of lift.c
in your folder.

**c29: Cayley graphs with involutions**: generating sets {t1, t2, t3, t4} (bouquet_4semi.txt) or {a, a^-1, t1, t2}
(bouquet_1loop_2semi.txt) in groups of order 2,186..2,400 with an index-2 subgroup and many involutions outside it
(G x Z2, dihedral-type products, AGL(1,p) x ..., S4 x ..., S3 x ...). Calibration: PGL(2,13) has order 2,184.

**c30: canonical double covers.** Cayley graphs of G x Z2 with generators (g, 1), i.e. bipartite doubles of non-bipartite
Cayley graphs of G with |G| in 1,093..1,200: G = meta (e.g. meta 55 20 2), psl2 7 x cyc 7, agl1 11 x cyc 10,
sl2 3 x cyc 46, psl2 5 x cyc 19. Compare with the Haar graph of the same G.

## Surgery and local search on explicit graphs

**c31: grow the 2,184 seed** (research/squads/b48/seeds/haar_meta_91_12_25_n2184.edges, VALID). Add vertices x (side A)
and y (side B): remove 3 edges a_i b_i, add x-b_i, y-a_i and x-y (degrees stay <= 4), then repair with local search
(2-switches that keep bipartiteness and degrees, or edge moves) minimising far pairs at n = 2,186. Write a fast C
evaluator (bit-parallel BFS like score48.c).

## Other two-orbit and non-lift constructions

**c32: coset graphs Cos(G; A, B)**: vertices = left cosets gA and gB, gA ~ hB iff gA and hB intersect; degree
|A : A cap B| and |B : A cap B|, both must be 4. Take A, B of order 4 (Z4 or Z2^2) with trivial intersection in groups
of order >= 4,372 (PSL(2,q) for prime q with |G|/4 >= 1,093, e.g. q = 23, 29, 31; metacyclic of order ~4,400..5,000),
or A, B of order 8 with |A cap B| = 2, etc. n = |G:A| + |G:B|. Search over pairs (A, B), score with score48.

**c33: bi-Cayley with loops.** Bases on 2 vertices with fewer parallel edges plus loops or semi-edges (degree 4 each):
"2 4 / 0 1 / 0 1 / 0 0 / 1 1" (2 parallel edges + a loop at each end) and "2 5 / 0 1 / 0 1 / 0 1 / 0 0 s / 1 1 s".
These lifts are bipartite only under a parity condition (lift checks it). Groups of order 1,094..1,200 with an index-2
subgroup (metacyclic with even k, agl1 p x ..., ...).

## Better search algorithms

**c34: a better annealer.** Improve on lift.c (copy it into your folder): targeted moves (pick an uncovered target and
choose the voltage change that reaches it), tabu, incremental evaluation, restarts. Benchmark time-to-cost-0 on
(dipole4, meta:91:12:25, N = 1,092; solvable) against the original with the same seeds, then run your best version on
meta 55 20 2 (N = 1,100) and on b22_t2.txt with a metacyclic group of order ~550.

**c35: genetic search over S** for metacyclic Haar graphs at orders 1,096..1,104: population of S, crossover = swap
generators between parents, mutation = small change of one component; fitness from `lift ... eval`. Compare with plain
annealing at equal evaluations.

**c36: exhaustive over the Z_m-parts.** For G = meta 55 20 2 (and meta 56 20 r, meta 110 10 r), fix the Z_20-parts
(j-parts) of S = {e, x, y, z} to the patterns used by the best annealed solutions (or to all patterns up to symmetry,
ranked by a quick score), and enumerate ALL Z_m-parts (55^3 = 166,375 sets per pattern; use `lift ... eval`, ~10 s per
pattern). Use automorphisms (a, j) -> (u a, j) to cut the count. This settles whether a pattern admits cost 0.

## Wildcards (find a direction none of the cards above uses; say which in "idea")

**c37: wildcard A.** Any construction or search not covered by c01..c36 and c40..c48.
**c38: wildcard B.** Same, but it must use a group or symmetry not mentioned in any card.
**c39: wildcard C.** Same, but no group acting freely: non-lift, non-Cayley constructions only.

## Algebra, geometry, analysis

**c40: incidence structures over GF(3) and GF(4).** PG(6,3) has exactly 1,093 = (3^7-1)/2 points and its lines have 4
points. A set of 1,093 lines with every point on 4 of them has a 4-regular bipartite incidence graph on 2,186 vertices
(girth >= 6). One Singer orbit of lines gives a cyclic Haar graph (abelian, fails). Look for better line sets: unions
of orbits of non-cyclic subgroups, lines from the split Cayley hexagon H(3) inside Q(6,3) plus extra lines, random
choices + local search. Also try Wenger / Lazebnik-Ustimenko D(k,4) and CD(k,4) graphs (4-regular, bipartite) and
modifications of them. Score with score48.

**c41: non-bipartite bases with a parity voltage.** Small 4-regular non-bipartite bases: K5 (b = 5), the octahedron
K_{2,2,2} (b = 6), circulants C_b(1,2), C_b(1,3), triangle with doubled edges, ... with groups of even order having an
index-2 subgroup, so that the lift is bipartite (lift checks this when the base is not bipartite). n = b*N >= 2,186.

**c42: linear groups of triangular / monomial type**: the Borel subgroup of GL(2,11) (upper triangular, order 1,100),
other upper-triangular or monomial matrix groups with order 1,094..1,250 (or 2,186..2,500 for Cayley graphs),
GammaL(1,q^2)-type groups. Build tables yourself (numpy), Haar-anneal with lift.

**c43: learn from smaller cells.** Find the best metacyclic Haar graphs at (4,6) and (4,7) (tables 728 and 840; we hold 864
at (4,7)) with haar_fast (`haar_fast 4 7 ...`), record which (k, ord(r), j-pattern of S) win there, and test whether the
same patterns give low cost at (4,8) for N = 1,094..1,150.

**c44: semidirect products Z_m x| Q with Q non-cyclic**: Q = Z_a x Z_b, S3, D4, Q8 or A4 acting on Z_m through a
homomorphism into the unit group Z_m^* (two independent units u, v for Q = Z_a x Z_b). Write your own table builder
((t, q)(t', q') = (t + phi(q) t', q q')). Orders 1,094..1,250. Haar-anneal with lift.

**c45: small non-abelian group x big cyclic**: S3 x Z183, D4 x Z137, Q8 x Z137, A4 x Z92, D5 x Z110, S4 x Z46,
SL(2,3) x Z46, A5 x Z19, D7 x Z79, Frobenius F21 x Z53, F20 x Z55, ... (orders 1,094..1,250). haar_fast `prod` where it
covers the family, else groups.py + lift.

**c46: anatomy of near misses.** For the best near misses (meta 55 20 2 at 1,100 and meta 137 8 10 at 1,096; get states
with lift's OUT), measure where words are wasted: collisions at each length (distinct values vs number of words),
short cycles (girth, number of 6- and 8-cycles). Then search only among S with fewer collisions (e.g. girth >= 8) and
report whether that helps.

**c47: girth-restricted search.** Haar graphs and 2+2 lifts of groups of order 1,094..1,150 where S must give girth >= 8
(no 6-cycles; check the relations of length 6) or girth >= 10. Generate such S and anneal within the constraint.

**c48: wildcard D (non-group).** Graph products, replacement or zig-zag products, gluing two (4,7)-type graphs with
bridging matchings, random 4-regular bipartite graphs with high girth plus local search, or anything else outside
lifts, Cayley and Haar graphs.
