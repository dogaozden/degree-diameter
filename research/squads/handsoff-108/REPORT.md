# handsoff-108: a hands-off Haiku squad on Δ10·D8 (final report)

Session: Opus coordinator, 2026-10-31 21:40 to 2026-11-01 03:30 UTC (5 h 50 min), branch
`claude/d10-d8-bipartite-search-c1gqpm`. Target: a bipartite graph with maximum degree 10, diameter 8 and more than
1,176,480 vertices (the table value, 30 copies of the split Cayley hexagon H(7)). The experiment: the Haikus do the work,
the coordinator only plans, checks in, verifies and redirects.

## Result

**No record.** Nothing reached cost 0, no worker claimed one, and `records/` is empty, so there was nothing to verify.
Closest states:
- Haar k = 3 orbit sets on PSL(2,23) × Z97 (2N = 1,177,968): energy 3 (one uncovered α-fixed element) once more
  (c7 reference run), energy 6 twice (c1 g2 on PSL(2,7) × SL(2,8) × Z7; c8c). Same depth as the 14,000 earlier
  descents (lowest 3), no deeper.
- A new graph family, bipartite coset graphs X(G, H, HgH): family K (G = PSL(2,229), H = D5, one regular double
  coset, 2N = 1,200,876) scanned completely, best member 4 uncovered vertices (class 4233, c6b-exhaust). Not verified
  by me, because it is not a solution.

## Spend (tools/session_usage.py, since 21:39:53Z)

At 03:24 UTC: Opus 0.619 budget units (99k output, 23.7M cache-read, 0.19M cache-write tokens, 103 messages); Haiku
0.286 units (2.17M output, 193M cache-read, 21.7M cache-write tokens, 1,201 messages), Haiku share 32 %. After my
last turns (writing this report) at 03:30: **Opus 0.663, Haiku 0.286, Haiku share 30 %**, short of the 50 % goal (last line
of `research/squads/usage/handsoff-108.jsonl`). The split stayed between 27 % and 33 % at every check-in.

Where my spend went: about 0.47 of my 0.62 units are cache reads, i.e. re-reading my own context (which grew to about
200k tokens) on each of 103 turns; my own output was 0.10. Waiting costs a turn every 10 minutes (the Bash cap), and
every turn re-reads the whole context. The Haikus produced 22× my output tokens and 8× my cache reads but cost
less than half as much, because Haiku tokens are priced at 1/40 of Opus here. To reach 50 % the coordinator needs a
much smaller context (compact or restart between check-ins) and fewer turns, not more Haiku work: the Haikus already
spent most of their wall time waiting on their own C programs.

## Haiku runs: 20 (8 at the start, 12 relaunches), plus 5 nudges

| run | card | size computed on | result | verdict |
|---|---|---|---|---|
| c1-grind | F15W3 grind, PSL(2,23)×Z97 and PSL(2,7)×SL(2,8)×Z7 (2 processes, 5 h 38 min) | Haar, N ≈ 590k | 448 + 442 descents, minima 9 and 6; pooled tail fit P(cost 0) ≈ 0.7-1.8e-4 per descent | baseline; showed that wall-clock schedules lose depth at load 7-8 |
| c2-repair | exact 1- and 2-orbit moves, fixed-letter swap, right multiplication from the best states | Haar | 5 states (two at energy 3): all exact local optima, no improvement | dead |
| c3-twist | twisted cyclic factor (tpgl, csl) to cut the abelian tax | Haar | tpgl worse (RANDORB median 345 vs 132); csl with n ≡ 2 mod 4 is SL × Z_{n/2}; stopped after 8 min | dead; one side lead |
| c3b-sl23x49 | descents on SL(2,23) × Z49 (c3's side lead) | Haar | 138 descents, min 12, median 24 (PSL(2,23)×Z97: 9, 21) | dead |
| c3c-grind | extra fresh-seed grind | Haar | 137 descents, min 12 | volume only |
| c4-groups | screen of direct-product groups in the window | Haar | PSL(2,29)×Z49 as good as the reference in RANDORB; 40 descents min 12; meta and n = 1 groups broken or slow; stalled at 22:39 and never handed back | inconclusive |
| c5-selfdual | twisted pairing S⁻¹ = β(S) with α of order 3 | Haar | far worse (best 113 vs 47 for standard orbits); the outer β my card asked for does not exist | dead |
| c5b-cosetscreen | screen of 14 coset-graph families | coset, N ≈ 590-600k | best family K (one regular double coset, h = 10); non-regular and h = 6 families 3-10× worse | lead (then closed by c6b) |
| c5c-scanC | exhaustive scan of coset family C (PGL(2,181), D5) | coset | 16,407 classes, minimum 44 | dead, exhaustive |
| c6-hexagon | voltage lifts of H(q) + two matchings | small: base 728-7,812 vertices, lifts ≤ 117k | reproduced the ten-level lemma; valid annealed lifts H(3)/Z24, H(4)/Z20, H(5)/Z15 (beats the 13-copy formula design); nothing at q = 7 | progress, other cells only |
| c6b-exhaust | exhaustive scan of coset family K | coset | 16,293 classes, minimum 4 (class 4233) | dead, exhaustive, closest new-family state |
| c6c-h12 | h = 12 coset families in PGL(2,193) | coset | my card's premise (one regular double coset) was wrong; A4/D6 families exhaustive, minima 501-1,266; C12 disconnected | dead, exhaustive |
| c7-throughput | schedules and early abort for the grind | Haar | no rule beats F15W3 at the sample sizes reachable; the reference run drew an energy-3 state | dead (inconclusive on the deep tail) |
| c7b-design | structure in the valid hexagon lifts | small: q = 3-5, one try at q = 7 | no formula; first-moment thresholds m* = 43, 34, 30, 29 copies for q = 3, 4, 5, 7 (table 20, 20, 25, 30), so the table's 30 at q = 7 must be structured; lifts invariant under a semiregular automorphism of H(q) beat plain annealing: 30 copies at q = 3 (21,840), 21 at q = 5 (164,052); q = 7 over Z43 reached cost 559 | progress, other cells only |
| c8-wild | its own idea: bipartite coset graphs X(G,H,HgH) | coset | built the family and first samples in 16 min | the squad's one new route |
| c8b-coset | fast evaluator + annealing on c8's family | coset | 10× faster cost (85 ms), caught its own pair-selection bug; annealed medians 11.5 units vs about 6-7 for Haar k = 3 | dead (3× worse than Haar) |
| c8c-smooth | secondary "fragility" term in the annealer | Haar | no detectable effect (p = 0.19-0.25, 75 descents) | dead |
| c8d-grind | extra fresh-seed grind | Haar | 88 descents, min 12 | volume only |
| c1b-structure | a cheap statistic that predicts good orbit sets | Haar | "no relation of length ≤ 3" separates good from random sets, but 84-95 % of descents reach it anyway; biased starts not significantly better (70 descents) | dead |
| c2b-digest | running digest for the coordinator | none | DIGEST.md every 25-30 min until 02:25 | useful; cut my reading |

All grinds of this squad together: 912 descents on PSL(2,23)×Z97, 442 on the product group, 217 on other groups,
no cost 0. At the pooled rate (about 1e-4 per descent) the expected number of hits was about 0.1.

## Did the hands-off structure do better or worse than an Opus-led squad?

For the record, no difference I can see: this cell is limited by compute, about 1e-4 per 50-second descent, and neither
structure changes that. For knowledge per Opus unit it did better. In under six hours it closed more directions, and
more of them for good, than an Opus-led session usually can: three complete scans of whole graph families (K, C, the
h = 12 families) with exact minima, two clean schedule and objective A/B tests, a group screen, and a structural
analysis of the hexagon lifts with a first-moment model. The one genuinely new route (coset graphs) came from a Haiku
wildcard. It went from idea (c8) to fast evaluator (c8b), screen (c5b) and exhaustive answers (c6b, c5c, c6c) in about
three hours, carried by cards I wrote from each hand-back. That chaining was the coordinator's main contribution.

What it did worse:
- **Stalls.** Five times a Haiku ended its turn "waiting on background work" with nothing running, and sat idle:
  c2-repair for 85 minutes, c7, c5b, c3b, and c4 (never resumed). A message wakes them, but only if I notice. Cards
  must tell them to poll with sleep loops and never end a turn while a run is going; after I added that line, the
  later runs kept going.
- **Premise errors go both ways.** Three of my cards had a wrong premise (c5: the outer β does not exist; c6c: no single
  regular double coset at h = 12; c3: csl with n ≡ 2 mod 4 is not twisted). The Haikus caught all three and said so,
  which is good. An Opus-led session would have hit the same errors while doing the work itself, before spending a card.
- **Bugs and units.** One annealer bug (c8b, caught and corrected by the worker itself), one batch of runs with the wrong
  ORBW (c2, discarded), and one note containing the word CLAIM that tripped my poller. No false claim reached
  records/.
- **Depth.** The Haikus answer the card's question and stop. None pushed a lead past its card, for example a local
  search from K's 4-uncovered class or longer q = 7 symmetric lift runs. Those need the coordinator to write the next card.

## Small structures vs large ones

The Haikus did best on the small-structure cards. c6 and c7b worked on base graphs of 728 to 7,812 vertices (lifts up to
164k), where one evaluation takes 0.6 s or less. They wrote their own evaluators and checkers, reproduced a known lemma,
built explicitly verified lifts, beat the lab's formula design at q = 5 (13 → 15 → 21 copies), and came up with
orbit-symmetric annealing on their own. None of it is in the target cell.

On the large cards (N ≈ 590,000 per side) they mostly drove existing tools (haar_sym2) or wrote one careful C program
and ran it. Their own code was correct and checked (fastc, exh.c, haar_c2, haar_c5, haar_smooth all validated
against references) but slow (85-130 ms per BFS against haar_sym2's 0.4 ms). They managed only a handful of
"run, look, fix" cycles in two hours. The large-graph cards that worked best were bounded exhaustive scans (about 16,000
classes, one hour of CPU), where a Haiku can finish and give a definite answer.

## What the graph size changed (compared with the 170- and 686-vertex sister squads)

I have not read the sister squads' results, so this says only what 1.18M vertices did here:
- **Code speed decides everything.** One exact evaluation costs 0.4 ms with the lab's bitset code and 0.1-1 s with
  code a Haiku writes in an hour; at a few hundred vertices both are microseconds. So a Haiku's loop of writing code,
  running it and looking at the result went from hundreds of iterations to five or ten per card.
- **Check cost.** A full check of a candidate takes minutes and gigabytes (haarcheck_gen, build_haar2.py), so workers
  rely on the search's own cost and the coordinator's verification is a separate, expensive step. Nothing needed it here.
- **Waiting is where the Haikus failed.** Most of their wall time was spent waiting for C programs, and that is exactly
  where the stalls happened. A small graph keeps a Haiku busy and in its turn.
- **How far they got alone.** Alone they could close a bounded question (a screen, an exhaustive family, an A/B test)
  but could not move the frontier of the target cell, which here needs about 1e4 CPU-hours of descents or an algebraic
  construction. At this size the structure (coordinator picks families, Haikus close them) works as a fast way to rule
  things out, not as a way to find a record.

## Files

`cards.md` (all 20 cards in order), `scoreboard.tsv`, `checkins.md`, `DIGEST.md`, one folder per run with NOTES.md,
code and logs; `shared/good_states.tsv` (119 low states from the earlier grinds), `shared/check.sh` (haarcheck_gen +
build_haar2.py). Binaries are not committed (`.gitignore`).
