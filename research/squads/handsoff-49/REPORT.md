# handsoff-49: a hands-off Haiku squad on the bipartite (4,9) cell

Session session_01QYEEyHVSftkeoMe7ftkrav, branch `claude/handsoff-49-bipartite-search-hy5axz`, 2026-10-31 21:36Z to
2026-11-01 about 03:20Z. Goal: a bipartite graph with maximum degree 4, diameter 9 and more than 4,970 vertices. Experiment:
Opus only coordinates (writes cards, checks in, verifies, redirects); Haiku subagents do the searching. Target spend
split about 50/50, measured by tools/session_usage.py.

## Result

**No record. The table value 4,970 stands.** No worker produced a graph with diameter 9 at n > 4,970, so nothing went to
`records/` and there was nothing for apsp.c to accept. The coordinator rebuilt the table graph itself at the start
(Haar graph of Z_71 x|_49 Z_35, S = {(0,0), (6,18), (30,19), (30,22)}; apsp VALID at D = 9, INVALID at D = 8;
`seeds/valid4970.edges`). Every near miss below was re-scored by the auditors w18 and w25 with score48 and apsp.

Best verified near misses (n > 4,970):

| n | measure | structure | worker | exact? | file |
|---|---|---|---|---|---|
| 4,972 | 160 far pairs | the 4,970 graph with 4 edges removed and 2 vertices added | w6 | no (annealing over the removed edges) | w6/tmp/surgsa4_best160.edges |
| 5,050 | cost 2 (2,525 far pairs) | Haar, Z_101 x\|_5 Z_25 | w2, w11 | yes, minimum over all S | w11/out/m101_k25_r5_c2.edges |
| 4,992 | cost 4 (4,992 far pairs) | Haar, Z_104 x\|_7 Z_24 and Z_208 x\|_3 Z_12; 2+2 lift over meta 13 96 5 / 39 32 31 | w2, w5, w11, w13 | yes for the two Haar groups | w13/best_haar_104_24_7_c4.edges, w5/out/t_mh2_1_1248_s31.edges |
| 5,000 | cost 4 (5,000 far pairs) | Haar, P x\| Z_4 of order 2,500 (P maximal class, exponent 5, order 625) | w15, w23 | yes (14 Aut-orbit reps, all pairs) | w23/NOTES.md (table in w15/tabs/u4m_7.bin) |
| 5,040 | cost 6 (7,560 far pairs) | Haar, A_7 | w1 | yes (exhaustive) | w1/t/A7_cost6.edges |
| 5,040 | cost 8 | Haar, S_5 x F_21 (centreless) | w10, w21 | yes (all 34 class reps) | w10/runs/S5xF21_cost8.edges |
| 5,040 | cost 15 (18,900 far pairs) | bi-coset graph of S_7, H an involution | w9 | yes | w9/runs/S7_h2_K2_full.edges |
| 5,200 | cost 30 | bi-coset graph of PSL(2,25), \|H\| = 3 | w7 | yes | w7/best_psl25_h3_C30_n5200.edges |

Full board: `scoreboard.tsv` (one line per improvement, 50+ lines). Audits: `w18/audit.tsv`, `w25/`. Per-worker
summary written by a Haiku: `w25/summary.md`. Check-ins: `checkins.md`. Cards: `cards.md`.

## Spend (tools/session_usage.py, price-weighted budget units)

At 03:11Z, after the last worker stopped (`python3 tools/session_usage.py --since 2026-10-31T21:36:27Z`, log in
`research/squads/usage/handsoff-49.jsonl`). About 10 minutes of Opus reading before the start stamp are not counted;
writing this report and the last commits add about 0.02 Opus.

| model | messages | output tokens | cache-read tokens | cache-write tokens | budget units | share |
|---|---|---|---|---|---|---|
| Opus (coordinator) | 96 | 147,140 | 20.3 M | 0.24 M | 0.614 | 58.5% |
| Haiku (26 workers) | 2,334 | 3,218,620 | 403.1 M | 24.6 M | 0.436 | 41.5% |
| total | | | | | 1.049 | |

So the split ended at about **58% Opus / 42% Haiku**, against the 50/50 target and the Opus-led squads' 97% / 3%
(research/squads/exp2/exp2-squad.md). The Haikus wrote 22 times as many output tokens as the coordinator and read 20
times as much context.

Over time (from checkins.md):

| time (Z) | Opus | Haiku | Haiku share | note |
|---|---|---|---|---|
| 21:42 | 0.06 | 0.00 | 0% | setup: prior work, tools, cards |
| 22:12 | 0.114 | 0.071 | 38% | 8 workers running |
| 22:40 | 0.148 | 0.117 | 44% | |
| 23:18 | 0.228 | 0.155 | 40% | writing round-2 cards costs Opus |
| 23:55 | 0.281 | 0.205 | 42% | |
| 00:25 | 0.343 | 0.245 | 42% | |
| 01:15 | 0.410 | 0.298 | 42% | |
| 02:03 | 0.472 | 0.362 | 43% | |
| 02:18 | 0.524 | 0.391 | 43% | 110 s rule sent at 02:10 |
| 03:11 | 0.614 | 0.436 | 42% | end; report writing |

The split stayed at about 42% Haiku for the whole run. Two things held it there:
- **Opus cost per check-in is fixed by context length.** Every Opus tool call re-reads the whole conversation (150-250k
  tokens late in the run), so even a 10-minute idle poll costs about 0.003 units, and writing a card plus launching a
  worker about 0.01. Opus spend grew at about 0.07 per hour regardless of what the Haikus did.
- **Haikus idled.** For subagents a foreground command longer than about 120 s is moved to the background and the Haiku
  ends its turn to wait. My cards said "timeout 540", so workers ran 9-minute searches and spent most of their time idle
  (w6, w10, w11 and w18 reported "waiting on background work"; w10 and w11 sat 25-30 minutes with nothing running until
  I nudged them). I learned the fix at 02:10 from the (3,7) sister squad (branch claude/handsoff-37-d3d7-r13gzx: "keep
  every command under 110 s" raised their Haiku rate about tenfold) and sent it to the 8 running workers, too late to
  change much here.

## Haiku runs

26 Haiku workers (w1-w26), each launched with one card and a 2-hour autonomous mandate (later ones until about 02:55Z),
plus 13 short coordinator messages to running workers (w6 resumed twice, w4 redirected, w10 and w11 nudged, the 110 s rule
to 8 workers). Median worker length about 95 minutes (range 14 minutes for w26, the benchmark, to 129 minutes for w4). Round 1:
w1-w8 (21:42Z). Round 2 was a rolling queue: each finished worker was replaced within minutes by a card built from what
the finished workers had learned (w9-w26).

## What each card found

Round 1 (my initial 8 cards):
- **w1 Haar, non-metacyclic groups, 2,486..2,700.** A_7 cost 6, exhaustive over every Haar set of A_7: minimum 6, so A_7 is
  ruled out. Other families floor at 7-10 (PGL(2,5) x Z_21 7, PSL(2,8) x Z_5 8). Lesson used later: low cost goes with a
  small centre and a small abelianization.
- **w2 Haar, all metacyclic groups of order 2,486..2,600** (1,779 split, 686 non-split). Best cost 2 (101 25 5, known),
  4 (104 24 7, known; 208 12 3, new), then 6. Nothing at 0.
- **w3 lifts of the GQ W(3) incidence graph (80 vertices)** over groups of order 63-80: valid up to n = 3,200 (Z_40), then
  the cost rises steadily with the group order (906 at Z_63). The number of constraints grows with the base.
- **w4 lifts of the GH H(3) incidence graph (728 vertices).** w4 proved my card impossible: H(3) has girth 12, so two
  vertices of one fibre of any lift are joined only through a closed non-backtracking walk of length >= 12, hence every lift
  has diameter >= 12. Redirected; best 6+6 random base over meta 13 32 5: cost 76.
- **w5 lifts of 5+5..8+8 bases** over groups of order 311-500: these floor at 100+. Smaller bases did better: 3+3 cost 19, 2+2
  base [[2,2],[2,2]] over meta 13 96 5 cost 4 at n = 4,992 (same as the Haar wall).
- **w6 surgery on the valid 4,970 graph.** 4,972 with 160 far pairs. Every edge of the table graph is critical for 168-179
  vertex pairs (in five different cost-0 solutions), and any 2-switch adds about 350 far pairs, so local search only goes
  uphill. Order-2,484 bases for a 4-vertex surgery all have cost > 0 (best 90).
- **w7 bi-coset graphs** (both sides cosets of H, edges by double cosets). PSL(2,25) with |H| = 3: n = 5,200, exact minimum
  30; PSL(3,3) 64; PSL(2,23) 88; PSU(3,3) 122. A central H only gives a Haar graph of G/H; perfect groups do best.
- **w8 wildcard.** 2+2 lift over AGL(1,13) x Z_8: cost 15 at 4,992; lifts of the (4,5) 162 graph over orders 31-40 stall at
  about 2,150. Tabu beat annealing by about 30%.

Round 2 (cards built from round 1):
- **w9 bi-coset, larger stabilizers.** Exact minima: S_7 with an involution 15 (n = 5,040), M_11 |H| = 3 38, PSL(2,25) 30,
  PSL(2,27) 176, A_8 |H| = 8 168, PSL(3,4) 354.
- **w10 centreless groups with small abelianization** (my list: A_5 x AGL(1,7), S_5 x F_21, Z_17^2 x| Z_9, Z_3^5 x| Z_11,
  ASL(2,5), ...). Best S_5 x F_21 cost 8; the others 22-2,296.
- **w11 exhaustive certification.** 33 metacyclic groups (split and non-split) exactly: minima 2, 4, 4, 6, ..., 10; no cost 0.
  Screened 281 groups of order 2,601..2,700 (best 10).
- **w12 lifts over simple groups with tabu.** PGL(2,11) 2+2: cost 64 at 5,280; PSL(2,11) 4+4 136; PSL(2,8) 5+5 136.
- **w13 the cost-4 wall at 4,992.** Haar diameter <= 9 iff (S^-1 S)^4 = G on both sides; in meta 104 24 7 the central
  involution (52, 0) is far in all 4,098 sampled states with cost <= 6, and forcing it covered costs >= 8. Groups without
  that involution (odd order, centreless, non-metacyclic) all did worse (8-72).
- **w14 bi-coset, large simple groups, |H| 6-24.** PSL(3,4) |H| = 8: 312; PGammaL(2,16) 453; others 936-14,616.
- **w15 order 2,500 = P x| Z_4** (my card). A maximal-class exponent-5 P of order 625 with an order-4 automorphism: cost 4
  at n = 5,000. Abelian P: 2,300+.
- **w16 quotients of the 4,970 graph.** The graph is a 5+5 lift over a group of order 497, a 7+7 lift over 355 and a 35+35
  lift over Z_71; all three rebuild it. But annealing and tabu could not re-find cost 0 on the 5+5 base over the order-497
  group (stalled at 68-98): for bases above 2+2 the optimizer, not the structure, was the wall. Re-lifts over bigger
  groups: best 82.
- **w17 mixed-orbit graphs** (G regular on A, stabilizers of order 2 or 4 on B). A_7 (4,4,4,4): 15,120 far pairs at
  5,040, worse than the Haar graph of A_7 (7,560).
- **w18 auditor.** 51 scoreboard lines re-scored: no VALID line above 4,970; three bookkeeping slips (an n written as N,
  an overwritten path, a file never written); the certified negatives re-run and matched.
- **w19 refinement ladder.** Viewed the cost-2 and cost-4 Haar optima as 3+3..8+8 lifts over index-k subgroups and searched
  the larger voltage space from them (annealing, tabu, far-pair moves, lookahead; about 40 runs). Every run stayed at its
  Haar start: one voltage change costs +30 to +90, so the Haar optima are isolated.
- **w20 certificate for metacyclic orders 2,486..2,520 (partial).**
  - Bound: an abelian Haar graph with S = {0, s1, s2, s3} reaches at most 309 values on one side within distance 8
    (brute-force count). So a metacyclic group with |G/G'| = k gcd(r-1, m) > 309 has no Haar graph of diameter 9.
  - After the bound, 901 classes remain (509 split, 392 non-split). 69 are certified with no cost-0 set: 46 by w20 (no
    set of cost <= 1, so minimum >= 2) and 23 already exact in w11. 832 are left, resumable with w20/run21.sh.
  - So the full certificate for 2,486..2,520 is not finished.
- **w21 exhaustive minima for the best non-metacyclic groups.**
  - Exact minimum 8 for S_5 x F_21 (all 34 class representatives) and for PSL(2,8) x Z_5 (all 44); both match their
    annealing floors.
  - Not finished: A_5 x S_3 x Z_7 (56 of 104 representatives, minimum 8 so far) and w15's order-2,500 group (6 of 123;
    w23 finished that one by another reduction: exact 4).
- **w22 wildcard.** Compound graphs (7 copies of H(3) minus a matching, 5,096: 81,619 far pairs) and mixed left/right
  bi-Cayley graphs behave like random graphs. Counting: same-side pairs get about 3.96 even walks of length <= 8 per
  target at this size, so random-like families miss about 2% of pairs.
- **w23 order 2,500 follow-up.** The cost-4 floor of w15's group is exact (all 14 Aut-orbit representatives, 3.1 M sets
  each, 1,160 sets at cost 4). Its wall is not a central involution: every cost-4 set leaves one inverse pair of
  order-20 elements uncovered on each side. Another order-2,500 group: floor 9 or 10.
- **w24 optimizer benchmark.** On w16's 5+5 base over the order-497 group: plain annealing 0 of 3 runs; a Z_5-symmetric
  ansatz (voltages equivariant under a base automorphism of order 5, 4 orbit representatives) reaches cost 0 in 13 of 40
  runs (about 3.5 s each). With that ansatz, 113 groups of order 498-530 (5+5) gave best 50 and 41 groups of order 356-380
  (7+7) best 119: no zeros.
- **w25 final audit and summary table** (w25/summary.md).
  - Re-checked all 57 scoreboard lines with score48, apsp and its own bitset reach-set code.
  - Scanned every edge file in the squad: all 1,408 files with n > 4,970 are INVALID (1,140 by diameter, 268
    disconnected).
  - Re-ran 26 of w11's certified lower bounds and w23's tallies, which all hold, and listed six bookkeeping slips (none
    affects a result).
  - Its Write of summary.md was refused for a subagent, so I saved its reply as that file.
- **w26 size benchmark** (w26/bench.md), used below.

## My view: hands-off versus an Opus-led squad

**On the result, no difference: neither finds a record here.** The big Opus-led squad on Oct 26 (48 Haikus per round,
research/squads/big-squad-4-8.md) stopped at the same walls: cost 4 at 4,992 and the proven cost 2 at 5,050. This squad
added certificates and structure, not a better graph:
- the exact minima of 33 metacyclic groups (w11), A_7, S_5 x F_21, PSL(2,8) x Z_5, an order-2,500 group and a dozen
  bi-coset classes, plus 46 more metacyclic groups with no Haar set of cost <= 1 (w20);
- a D = 9 abelian-quotient bound (309);
- the H(3) impossibility proof;
- the (S^-1 S)^4 = G description of the cost-4 wall, and a different wall at order 2,500;
- the isolation of the Haar optima in every larger k+k voltage space;
- the finding that plain optimizers fail on 5+5 bases where a solution is known, while a symmetric ansatz succeeds.

**Where hands-off was better.** Breadth with depth: 26 workers of about 95 minutes each ran far longer, more careful
searches than 6-8-minute cards in a crowded squad. The Haikus wrote their own exhaustive searches with automorphism
reduction (w1, w11, w23), built hard groups by hand without GAP (M_11, PSL(3,4), Sz(8), PSU(3,4) as permutation groups; a
maximal-class 5-group of order 625 inside U_4(F_5)), and found real things on their own:
- w4's girth argument, which corrected my card;
- w13's characterization of the cost-4 wall;
- w24's symmetric ansatz.

They also corrected each other through shared files (w19 used w16's code, w23 and w21 continued w15 and w10).

**Where it was worse.** (1) Steering lags: I see a worker's result only when it hands back or at a check-in, so a dead end
(the H(3) card, the cyclic lifts w4 drifted into, idle workers) runs 20-40 minutes before I act. An Opus director doing
its own work notices in minutes. (2) The decisive moves in the earlier Opus-led runs were director moves (new tools,
exhaustive proofs); here they were mine only at card level. The new ideas in round 2 (centreless groups, order 2,500,
quotients of the table graph, mixed-orbit graphs, the refinement ladder) came from me, and the Haikus executed them well
but did not escape the walls. (3) The 120 s background rule cost a lot of Haiku time before I knew it. (4) Haikus
sometimes stopped early or drifted to an easier sub-problem when the card's main line failed, and some bookkeeping
slipped, which is why two audit workers were worth their cost.

An Opus-led squad would probably have reached the same "no record" with fewer total tokens and fewer wall-clock hours,
because Opus would have run the exhaustive certifications itself and pruned dead families sooner. The hands-off structure
bought more independent, documented negative results per Opus token: the Opus side here was mostly reading and writing
cards (0.07 units per hour), not computing.

## Small structures versus large ones

The Haikus did much better on the small-structure cards:
- **Small (strong results):** Haar graphs of one group at a time, 2+2 and 3+3 lifts, exhaustive certification of fixed
  groups. Best results (costs 2-8) and all the exact certificates.
- **Large (far from the target):** the 80-vertex W(3) base, the 728-vertex H(3) base, 5+5 to 8+8 bases, the 35+35
  quotient, bi-coset graphs of large simple groups with big stabilizers, compound graphs. These ended at costs 50-14,000.

Two reasons, both measured:
- **The constraints grow with the base and the variables do not** (w3). A k+k base over a group of order N has k+1 free
  voltages but about 2k roots times n targets to cover.
- **Generic optimizers fail in big voltage spaces even when a solution exists** (w16, w24). Plain annealing never re-found
  the known cost-0 lift on a 5+5 base; a symmetric ansatz found it a third of the time.

So the large-structure cards were limited by search method more than by structure, and only one Haiku (w24) found the fix
(symmetry), late.

## What the graph size changed (4,970 vertices here, versus 170 for (3,7) and 686 for (6,5))

From w26's benchmark on this machine under the squad's load (w26/bench.md):

| size | apsp check (median) | Haar candidate evaluations | evaluations to re-find a known solution |
|---|---|---|---|
| (3,7), n = 168 | 3.3 ms | 862 k/s | 1-9 (N = 55) |
| (6,5), n = 686 | 3.8 ms | 823 k/s | about 10 k (N = 272, 0.2 s) |
| (4,9), n = 4,970 | 38.9 ms | 12.8 k/s | about 462 k (5 s) |

- **Code speed.** One candidate costs about 65 times more at (4,9) than at the smaller cells. A Haiku's 100-second run
  covers what takes 1.5 s at (6,5).
- **Check cost.** A full independent apsp check is about 10 times dearer but still negligible (39 ms), so verification
  was never the bottleneck. Exhaustive searches of one group of order about 2,500 took 1-15 minutes each and were the
  natural unit of Haiku work.
- **How far they got.** At (3,7) the sister squad's Haikus reached 46 far pairs at n = 170 and rediscovered a known near
  miss from scratch. Here the Haikus reproduced every earlier near miss (costs 2 and 4) and certified them, but at this
  size each idea costs minutes, not seconds. More of their effort went into building groups (no GAP in the container) and
  into waiting on runs.
- **Spend split.** The long runs and the 120 s background rule kept the split near 42% Haiku, against 66% at (3,7)
  once that squad used short commands.

The (6,5) sister squad's report was not on the remote when this was written, so the 686-vertex column comes only from
w26's benchmark.

## Housekeeping

- w17 reported that it accidentally created an empty remote session (session_01QYEEyJsYywiVk2TbEp9qgL) with a
  no-argument create_session call. I did not archive it; it can be archived from the session list.
- Group tables (*.bin, w*/tabs/) and compiled binaries are not committed (.gitignore); every worker's NOTES.md has the
  commands that rebuild them.
