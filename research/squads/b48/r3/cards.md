# Round 3 cards (20). Read HEADER.md first. Folder: research/squads/b48/r3/<card>/

Cards d01..d16: cell (4,9), D = 9, target n >= 4,972 (group order N >= 2,486 for Haar graphs). Cards e01..e04: cell (4,8).
T = /home/user/degree-diameter/research/squads/b48/tools, B = the scratchpad bin dir in HEADER.md.
Screening protocol unless the card says otherwise: haar_fast (or haar_tab) 8-10 s per group with seed 1, then the best
three for 60 s on 2 seeds. Put "cell": "4,9" or "4,8" in your scoreboard line. A valid (4,9) claim needs
`$T/score48 FILE.edges 4 9` = RESULT VALID (for haar_fast solutions: build_haar2.py SOL OUT.edges, then score48).

## (4,9): metacyclic Haar graphs, by slice

**d01: Frobenius metacyclic Z_p x| Z_k, k | p - 1, N = p k in 2,486..2,900.** E.g. Z_101 x| Z_25 (2,525; the director
already runs it exhaustively, skip it), Z_73 x| Z_36 (2,628), Z_53 x| Z_52 (2,756 = AGL(1,53)), and all others in range
(also p k with k a proper divisor of p - 1). List them all, screen, push the best.

**d02: metacyclic with composite m and large faithful k (k >= 20)**, N in 2,486..2,800, r of order exactly k, gcd(r-1, m)
small (1 or 2). E.g. meta 104 24 7 (cost 4), meta 105 24 17 (cost 6). Screen all classes, push the best.

**d03: metacyclic with k in 12..19**, N in 2,486..2,800, same filters (ord(r) >= 6, gcd(r - 1, m) <= 2). E.g. meta 208 12 3
(cost 4). Screen, push the best.

**d04: metacyclic with k in 6..11**, N in 2,486..2,800, same filters. Screen, push the best.

**d05: exhaustive certification.** For the best groups of d01..d04 that satisfy gcd(r - 1, m) = 1 (other than meta 101
25 5), run the exhaustive search (`exh_meta.py` | `flift ... eval`, LIMIT=2 ONLYLOW=1, split with --slice if needed). If a
cost-0 S appears, build the edge list (`flift` writes nothing in eval mode: make the edges yourself from S with
(0,x) ~ (1, s*x) for s in S, left multiplication in meta:m:k:r indexing a + m*j, or rerun flift's annealer from that S)
and check with score48 4 9. Report the minimum per group.

## (4,9): other group families

**d06: abc (abelian-by-cyclic, non-metacyclic) groups**, N in 2,486..2,900 (`abc.py list 2486 2900 --nonmeta`, plus @e
root variants for repeated primes). haar_tab with D = 9. Screen, push the best.

**d07: SL/PSL/PGL(2,q) x Z_n with haar_fast**, N in 2,486..2,900: e.g. sl 7 8? (check orders), psl 7 15 (2,520),
sl 5 21 (2,520), psl 8 5 (2,520), psl 9 7 (2,520), psl 11 4 (2,640), pgl 7 8 (2,688). Mind the involution rule: SL has
one involution, PSL many; odd n is better. Screen, push the best.

**d08: AGL(1,q) x Z_n with haar_fast** (`agl1 q` then n), N in 2,486..2,900: agl1 53 1 (2,756), agl1 13 16 (2,496),
agl1 16 11 (2,640), agl1 49 1? (2,352, too small), agl1 7 60, agl1 11 23 (2,530), agl1 5 125, agl1 9 35 (2,520), ... List,
screen, push the best.

**d09: direct products and semidirect products not covered above**: Frobenius group x small group (e.g. (Z_101 x| Z_25)
is 2,525 already; F_21 x meta(~119), F_55 x meta(~46)...), Z_p^2 x| Z_k, SL(2,3) x meta, ... N in 2,486..2,900, haar_tab.

## (4,9): lifts with more fibres and other shapes

**d10: 2+2 lifts with flift at D = 9** ($T/bases/b22_t1.txt, b22_t2.txt; n = 4N, N in 1,243..1,400): metacyclic
Frobenius-type groups and abc groups. Screen 10 s, push the best for 60 s.

**d11: 3+3 and 4+4 lifts with flift at D = 9** ($T/bases/k33_matching.txt, other 3+3 classes in
research/squads/b48/r1/c20/, $T/bases/k44.txt; N in 829..950 for 3+3, 622..700 for 4+4). Screen, push the best.

**d12: Cayley graphs at (4,9)**: bipartite Cayley graphs of groups of order 4,972..5,600 with an index-2 subgroup
(e.g. meta with even k; generators outside the index-2 subgroup) using lift with bouquet bases (lift checks bipartiteness)
or your own evaluator. Round 1 found Cayley graphs weak at (4,8); test whether that holds at (4,9).

**d13: the involution rule at D = 9.** Compare, on a few groups of order ~2,500, the cost with many involutions (e.g. odd
m with k even) and with none (k odd). Use the result to pick 10 more groups with few involutions and screen them.

**d14: below the 2,496 gap.** Orders 2,486..2,495 have no good metacyclic group. Look for any other group of these orders
(abc, products, matrix groups, permutation groups) that could give n = 4,972..4,990, and screen it.

## Wildcards

**d15: wildcard (4,9).** Any direction not covered by d01..d14. Say which in "idea".
**d16: wildcard (4,9), analysis first.** Study the best near misses (e.g. haar_fast on meta 104 24 7: why exactly 4?) and
design the next group or construction from what you find.

## (4,8) cards

**e01: (4,8) exhaustive certification.** Run exh_meta.py (D = 8) on the 15 best metacyclic groups of order 1,093..1,130
with gcd(r - 1, m) = 1 from r1/scan_meta_1092_1120.txt and round-1/2 reports, and report the true minimum of each. One
group of order ~1,100 takes ~30 s. This turns "annealing floor" into a theorem per group.

**e02: (4,8) multi-fibre lifts with flift and Frobenius groups**: bases with b = 4, 6, 8 (2+2, 3+3, K44) and Frobenius or
abc groups of order >= 2,186/b (e.g. Z_p x| Z_k with k | p - 1). Round 2's best 2+2 lift was cost 22.

**e03: (4,8) Haar graphs of groups of order 1,152 and 1,200 beyond round 1**: build many solvable groups of these orders
as permutation groups or semidirect products (e.g. Z_3^2 x| Q with Q of order 128 or 16, (Z_2^4 x| Z_9) x ..., Z_5^2 x| Q
with |Q| = 48), screen with haar_tab, push the best.

**e04: (4,8) wildcard.** Anything not tried in rounds 1-2 (read r1/cards.md and r2/cards.md first).
