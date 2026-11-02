# deep-49: an Opus-led squad on the bipartite (4,9) cell

Session session_01QYEEyH81pZHeSQtpD99oPr, branch `claude/deep-49-bipartite-cell-3tog1a`, 2026-11-01 22:39Z (start stamp
`research/squads/usage/deep-49.start`) to about 02:00Z. Goal: a bipartite graph with maximum degree 4, diameter 9 and
4,971 or more vertices (table 4,970). Brief: depth on the hands-off run's leads (handsoff-49): the cost-2 Haar graph at
5,050 ("(b)"), the cost-4 walls at 4,992 and 5,000, and the 2-vertex surgery at 4,972 with 160 far pairs ("(a)").

## Result

**No record. 4,970 stands.** Nothing went to `records/`. What changed is that most of the leads are now closed by exact
searches instead of annealing floors, and each floor has a concrete reason:

| lead | hands-off (heuristic) | deep-49 (exact or exhaustive) |
|---|---|---|
| Haar graphs, all groups of order 2,486..2,600 in GAP's SmallGroups library | metacyclic only, screened | **none has diameter 9** (67 groups searched exhaustively, the other 96 excluded by the abelian-quotient bound) |
| metacyclic Haar graphs, orders 2,486..2,530 missing from the library | 46 groups certified "no cost <= 1" | all 263 split groups (d >= 3, \|G/G'\| <= 309) exhaustive: no cost 0 |
| non-metacyclic solvable, missing orders | a few by hand | 368 groups exhaustive: no cost 0 (partial coverage, see below) |
| non-solvable, order 2,520 | A7 6, S5 x F21 8, PSL(2,8) x C5 8 | all 18 groups listed below exhaustive; **new best SL(2,5) x F21: exact minimum 4 (n = 5,040)** |
| (b) 5,050, Z_101 x\| Z_25 | minimum 2 | minimum 2 with 2 isomorphism classes; the missed pair always lies in the conjugacy classes y^(+-6) or y^(+-9) (cosets of the kernel), never in the kernel; parity lemma explains why 2 and not 1 |
| 4,992 walls | central involution always far (sampled) | **exact: all 184 / 96 cost-4 sets miss the central involution on both sides; forcing it costs 8 / 12** |
| (a) surgery at 4,972 | 160 far pairs (annealed) | **149 by design**, exhaustive over all 41,040 "linked" designs; every remaining far pair is a slack-0 critical pair of a deleted edge |
| hub types (point stabilisers) | bi-coset of simple groups 15-30 | bi-coset of Frobenius / metacyclic groups: >= 16 (exhaustive); one-sided stabilisers and cubic-Haar-plus-hubs: screens 17-30 |

Verified graph files (all apsp-checked by me): the record rebuilt from hx's output (`seeds/valid4970.edges`, VALID at 9,
INVALID at 8) and a new diameter-9 Haar graph below the record, Z_61 x|_8 Z_40 at n = 4,880 (`r2/c/g2440_61_40_8.edges`,
VALID at 9, INVALID at 8). Best surgery: `analysis/tree_best.edges` (n = 4,972, 149 far pairs, sha256 d37dd2c5...).

## Tools I wrote (research/squads/deep-49/tools/, README.md there)

- **hx.c**: exact search for Haar graphs H(G,S), |S| = 4, over any group given by a multiplication table, reduced by
  Aut(G) (the normaliser of the regular representation): x over Aut-orbit representatives, y over orbit
  representatives of Stab(x) (Schreier generators), z over all elements with orbit index >= that of y; a "killer list"
  of recently missed elements rejects most sets after a few membership tests. It reproduces the record group in 11 s
  (24 cost-0 hits, as w11 found), Z_101 x| Z_25 "no cost <= 1" in 10 s and Z_104 x| Z_24 "no cost <= 3" in 16 s.
- **GAP export** (export_group.g, build_tab.py): any GAP group to a table plus Aut(G) generators for hx. GAP 4.12 was
  installed in the container with apt (the hands-off squad had no GAP and built groups by hand).
- **bicos.c**: bi-coset graphs of Frobenius groups with point stabilisers (exhaustive); **mixed.c** (one side
  regular, the other two orbits with stabilisers of order 2); **hubs.c** (cubic Haar graph plus one hub orbit per side,
  stabilisers of order 4); **capacity.c** (formal word count by twist order); analysis/critslack.c, pathsurg.c,
  treesurg.c, classify_surg.py for the surgery.

## (b) The 5,050 Haar graph and its generalisations

**Why 2.** G = Z_101 x|_5 Z_25 is a Frobenius group; its conjugacy classes outside the kernel K = Z_101 are exactly
the cosets K y^j (j != 0), so a "class" here is a fibre of G -> G/K = Z_25. hx with LIMIT 6 gives the cost histogram
(canonical sets): 0 at cost 0, 48 at cost 2, 24 at cost 4, 120 at cost 6. The 48 cost-2 sets fall into 2 classes by
distance-distribution invariants. Card c4 tabulated them: each misses exactly one inverse pair {g, g^-1} on one side
only, always in the classes j = +-6 or j = +-9, never in the kernel. The minimum is even because (SS^-1)^4 is closed
under inversion and G has odd order, so misses come in inverse pairs (c4's lemma): 2 is one missed pair, the least
possible non-zero cost.

**Which double cosets could cover the two missing classes.** None that this group offers. With K normal, the
(K,K)-double cosets are the cosets K y^j, and every cost-2 set already reaches all but one element of the two missed
cosets; covering that element needs a different S, and the exhaustive search says every S misses something. The
double-coset (bi-coset) generalisation inside AGL(1,101) = Z_101 x| Z_100 with point stabiliser Z_h gives n = 5,050 for
h = 2 (Z_101 x| Z_50) and h = 4 (Z_101 x| Z_100); since gcd(h, 25) = 1 both are Haar graphs of Z_101 x| Z_25 with an
h-invariant S, a subfamily, so they cannot do better than 2 (card c6 found 16 there, exhaustively).

**Fibre counts.** For S with j-parts {0,3,7,15} the formal word count per fibre is 372-415 (total = 9,841, the Moore
count: no forced coincidences at all), and the actual multiplicities in the missed fibre are 3-12 with a single 0. So
the miss is not a shortage of words in a fibre but a collision pattern: the minimum is luck, not a structural wall.
The record is the same kind of object: its group has a single cost-0 graph up to the invariants (24 canonical hits, one
class), and that graph has girth >= 10 (its same-side layer sizes are 1, 12, 108, 902, 1,462 against the Moore
1, 12, 108, 972, 8,748).

**Generalising to other groups (exact, reduced by the normaliser).**
- Every group of order 2,486..2,530 and 2,531..2,600 that GAP's SmallGroups library has: 163 groups; 96 have
  |G/G'| > 309 or abelian rank > 3 and are impossible (a Haar graph of an abelian group reaches at most 309 elements on a
  side within distance 8, the FCC count 1 + 12 + 42 + 92 + 162; w20's bound); the other 67 were searched with hx:
  none has a cost-0 set (`results/smallgroups_*`).
- Orders missing from the library (2,488, 2,490, 2,492, 2,496, 2,499, 2,500, 2,502, 2,504, 2,508, 2,511, 2,512,
  2,516, 2,520, 2,528, 2,530): card c2 certified all 263 split metacyclic groups (d >= 3, |G/G'| <= 309); card c7 368
  non-metacyclic solvable groups built as semidirect and direct products; cards c1 and r2a every non-solvable group of
  order 2,520 we could list (A7; A6 x C7; PSL(2,7) x C15; SL(2,5) x C21 and x F21; A5 x X for the six groups X of
  order 42 and A5 x C7 x S3; S5 x C21, S5 x F21; the fibred products S5 x_C2 X for X = D21, C7:C6, C3 x D7, C7 x S3;
  PSL(2,8) x C5 from handsoff) plus A5 x C43 (2,580) and PSL(2,11) x C4, x C2^2 (2,640). No cost 0 anywhere.
  Exact minima: SL(2,5) x F21 4, A7 6, S5 x C21 7, A6 x C7 8, S5 x F21 8, A5 x C7 x S3 8, A5 x C2 x F21 9,
  PSL(2,7) x C15 10, the rest > 8 or > 10. Not covered: groups of order 2,496 and 2,500 beyond direct products and
  sampled P:C4 actions, some solvable 2,520 groups, non-split metacyclic groups of the missing orders.
- Capacity by twist (tools/capacity): for a metacyclic group whose kernel action has order d, |(SS^-1)^4| is at most
  309, 1,849, 4,429, 6,157, 7,581, 8,441, 9,003, 9,281 for d = 1..8 (9,793 at d = 12; 9,841 is the Moore count).
  So d <= 2 is impossible above 1,849 and small d is hopeless near 2,500, where the record needs 9,841 / 2,485 = 3.96.
- The luck curve (exact minima; c3 and r2c): among the 22 Frobenius groups Z_p x| Z_k of order 2,200..2,800 only three
  have cost 0, at 2,211 (67:33), 2,265 (151:15) and 2,485 (71:35); 2,329 (137:17) and 2,525 (101:25) reach 2; the rest
  8 or more. Among the 46 split metacyclic groups of order 2,440..2,485 with d >= 8, only 2,485 and 2,440 (61:40, new,
  n = 4,880) have cost 0. Cost 0 at this size is a rare event even below the record, and no group above it has one.

**Hub types.** Point stabilisers hurt. Bi-coset graphs (stabiliser on both sides) of Frobenius groups: every non-Haar
case with n in 4,972..5,600 is far worse than Haar (best 88 far vertices from two roots, exhaustive, bicos); card c6
extended this to composite kernels (6,047 families, exhaustive where feasible): best 16 at 5,050, which is a Haar
subfamily, and 28 for a genuinely non-Haar one (n = 5,256). One-sided stabilisers (mixed.c) and the cubic Haar graph
with hub orbits (hubs.c) screen at 17 at best (Z_125 x| Z_20, against an exact Haar minimum >= 13 for that group; A7 21 against Haar 6) and the
hub orbits at 25 at best (PSL(2,7) x A4, n = 5,040), over 44 groups (card r2b; screens, not exhaustive). The reason is
visible in the bi-coset case (one reason, not a proof): a stabiliser that fixes the root also fixes some vertices of its ball, and every walk to a
fixed vertex is doubled, so the root's ball is smaller than in a Haar graph of the same size.

## The walls at 4,992 and 5,040

Card c4 (exact, hx with a "must cover" option): for Z_104 x|_7 Z_24 all 184 cost-4 sets miss the central involution
z = (52, 0) on both sides, and the other two misses are an inverse pair in fibre +-6; requiring z covered raises the
minimum to 8 (on one side only: also 8). For Z_208 x|_3 Z_12 all 96 cost-4 sets miss z = (104, 0) on both sides;
forcing it costs 12. So the 4,992 wall is exactly the central involution, as w13 guessed from samples. The new 5,040
near miss SL(2,5) x F21 is a different kind (r2a): its cost-4 sets never miss the central involution or any element of
order 2; they miss a pair of order-30 elements, or elements of orders 12 and 3; covering all order-30 elements still
allows 4, covering orders 12 and 30 forces 8.

## (a) Inserting two vertices into the 4,970 graph

**Why each deleted edge costs about 170 pairs.** For the four edge types of the record (analysis/critslack_4970.txt),
deleting one edge makes 168-179 pairs far; all but one are same-side pairs, and about half of them (86-97) have slack 0
(they were at distance exactly 8 and every 8-path used the edge). A surgery replaces the edge a_i b_i by detours through
a* and b*. A detour has length at least 3, so it repairs a critical pair only if the pair had slack >= 2; a slack-0 pair
needs a genuine shortcut, that is, one of the other new neighbours within distance beta-1 of one end (beta = the end's
distance to the edge). For the "balanced" slack-0 pairs (both ends at distance >= 2 from the edge; 33-41 per edge) that
means a new neighbour within distance 2-4 of a specific vertex: with only six other new neighbours, most stay far.

**Design instead of annealing.** The annealed 160-pair surgery of the hands-off squad turns out to have a clear
structure (reproduced here: 161): its four deleted edges are the 1st, 3rd, 5th and 7th edges of a path of length 7, so
every deleted edge has a detour of length 3 through a kept path edge and a new vertex. (A 6-cycle would be the natural
"closed" version, but the record has girth >= 10.) Exhaustive design searches:
- alternating paths of length 7 from a fixed vertex (2,916 designs; vertex-transitivity makes this all of them): best
  **149** (pathsurg); with 3 deleted edges and the edge a*b*: 167;
- all "linked" designs, where each deleted edge is joined to an earlier one by a kept edge (41,040 distinct designs,
  treesurg): best **149** again (card c5 independently reached 149 with three deleted edges plus the edge a*b*, by design and
  single swaps);
- card c5's twin designs (a* copies a vertex's neighbourhood): 775 and 794; three twins plus a*b*: 205 / 217; mixed
  families: 294.
In the best design all 149 far pairs are slack-0 critical pairs of the deleted edges (27 with split (0,7), 41 (1,6),
32 (2,5), 32 (3,4)) plus 17 pairs at the new vertices (analysis/classify_surgeries.txt). The detour design kills every
critical pair with slack >= 2, and the slack-0 pairs are what is left. A 2-vertex surgery on this graph cannot get
near 0: it would need about 140 shortcut repairs from six vertices.

## Squad rounds and the Opus / Haiku split

Opus did the thinking and wrote the tools and cards; 14 Haiku subagents ran cards (8 in round 1 at 23:10Z, 5 rolling
in round 2 as slots freed). Every card was an exact search or an exhaustive design family scored by hx / score48 / apsp,
and every command was kept under 110 s (no Haiku idled in the background this time).

| round | cards | what came back |
|---|---|---|
| director, before the squad | hx, GAP, SmallGroups sweep, bicos, capacity | 67 groups of order 2,486..2,600 certified; bi-coset Frobenius >= 88 |
| r1 (8 Haikus, 23:10-00:20Z) | c1-c8 above | SL(2,5) x F21 = 4 (new); 263 + 368 groups certified; wall structure at 4,992; luck curve; surgery 149 |
| r2 (5 Haikus, 23:35-01:00Z) | r2a-r2e | non-direct 2,520 groups > 8; mixed / hub screens 17 / 25; 4,880 cost 0 below the record; audit 8 of 9 confirmed; [r2e] |
| director, during the squad | design searches, slack analysis, verification | surgery 149 exhaustive over 41,040 designs; every claimed VALID graph re-checked with apsp |

Verification: every graph called VALID here was checked by me with tools/apsp.c (the coordinator's apsp.c) at D = 9 and
D = 8. The auditor card (r2d) re-ran the main exact claims with the hands-off squad's independent exh3.c (inner
automorphisms only): record group cost 0, 5,050 minimum 2, SL(2,5) x F21 minimum 4, 4,992 constrained minimum 8, two
random ">0" groups; all agree (one more was too slow to finish). It also found one latent flaw in hx.c, an early reject
(|X|^2 < N) that is only exact for LIMIT < N - floor(sqrt(N-1))^2 (20 or more for every N used); no run was affected
(all used LIMIT <= 12), and the check is now exact for every LIMIT.

Spend (tools/session_usage.py --since 2026-11-01T22:39:07Z --arm deep-49, log research/squads/usage/deep-49.jsonl):

[usage table]

## Comparison with the hands-off run on the same cell

[fill in]
