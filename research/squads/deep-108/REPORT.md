# deep-108: an Opus-led depth run on Δ10·D8 (final report)

Session: Opus coordinator with a small Haiku squad, 2026-11-01 22:39 UTC to 2026-11-02 01:13 UTC (stopped early by Doğa for budget, after 2 h 34 min), branch
`claude/d10-d8-depth-search-3b5yyu` (draft PR #528). Target: a bipartite graph with maximum degree 10, diameter 8 and
at least 1,176,481 vertices (table 1,176,480 = 30 copies of the split Cayley hexagon H(7)). Brief: the depth the
hands-off run (handsoff-108) lacked, on its two leads: (a) the energy-3 orbit states on PSL(2,23) × Z97, (b) the coset
family K (PSL(2,229), H = D5, one regular double coset, exhaustive minimum 4).

## Result

**No record.** No search or scan reached cost 0, and `records/` is empty. What the run established:

1. **Why K's minimum is 4, exactly.** The 4 uncovered vertices of K's best class (4233) are two of the eleven
   size-2 orbits of H on B-vertices: cosets in the normaliser of C5. Every one of the 59,985 regular orbits and all
   113 size-5 orbits are covered. Special orbits (stabiliser ≠ 1) are covered by about λ·s/10 independent walk-orbits
   (s = orbit size, λ = 8.96), so they are missed with probability e^(−λ s/10): 0.17 for size 2. K's expected
   special misses are 3.5, so even a class with every regular orbit covered has only about a 3 % chance of cost 0.
   4233 was that class, and it lost that coin flip on two of eleven orbits. Within degree 10 no other double coset
   can be added to cover them: the single regular double coset uses the whole degree, and changing z changes the whole graph.
2. **(b) does not generalise to a record anywhere near the bound.** All degree-10 one-double-coset families with
   vertex stabiliser of order 10 in groups of order 5.9–6.2 M are now closed (table below). Larger stabilisers
   (h = 20, 60) force a non-trivial edge stabiliser, and those families have about 135 members and are far worse.
   The "bi-coset" trick (different subgroups L ≠ R on the two sides) removes special orbits when L and R share
   no conjugate elements. It gave the first family with no special orbits at all (A5 × PSL(2,59)), but its regular-orbit
   tax is higher than K's, so it is not better.
3. **Why the families are taxed.** Median members leave 4.4 (K) to 6.7 (C) times the uncovered vertices of the
   independent-walk model. The excess is a positive correlation in the coverage of the ten neighbours of a vertex
   (overdispersed against a binomial; k = 0 occurs 6.6 times too often). It is not short cycles, not fibres of
   the overgroup N(C5), and only about 10 % of it is explained by B-vertices whose stabiliser moves the root by 2.
4. **(a) is a compute lottery with no design lever found.** The energy-3 states have every free orbit covered and
   miss one α-fixed element. Fixed elements are hit only by α-symmetric triples of words, so each is missed with
   probability about e^(−λ/3). No local move repairs them: they are exact local optima under single-orbit
   replacement (earlier sessions), and swapping the fixed letter e for any other α-fixed element costs 36–157 (this
   run). Inserting vertices cannot help: one uncovered group element is |G| = 588,984 bad pairs, against a slack of
   1,487 vertices.
5. **A tool.** `cq` evaluates bi-coset graphs by BFS on the root stabiliser's orbits: 17 ms per A-root BFS on K,
   against 130 ms for handsoff's exh.c, validated on 200 random K classes. With the normaliser reduction
   D → aDb⁻¹ it also gives exact counts of distinct graphs (K 16,293; C 8,226, not 16,407 as reported by the hands-off run).

### Every one-double-coset family with vertex stabiliser of order 10 near the bound

N = |G|/10 vertices per side (2N must exceed 1,176,480); μ/h = N e^(−5,380,840/N)/10 is the independent-walk mean of
uncovered regular orbits; medians and p0.1 are over members with uBA + uAA < 20,000 (connected); E_s = expected special-orbit misses (from the census, λ = 5,380,840/N); "classes" = distinct
graphs after the normaliser reduction (an upper bound). Cost = exact minimum over the whole family, in vertices.

| G | L, R | N | μ/h | E_s | classes | min cost (orbits missed) | median | who |
|---|---|---|---|---|---|---|---|---|
| PSL(2,229) | D5, D5 (K) | 600,438 | 7.7 | 3.5 | 16,293 | **4** (0 regular + 2 of size 2); p0.1 55 | 344 | handsoff c6b; analysed here |
| PGL(2,181) | D5n, D5n (C) | 592,956 | 6.8 | 5.5 | 8,226 | 44 | ~450 (sample) | handsoff c5c |
| PGL(2,181) | D5s, D5n | 592,956 | 6.8 | 2.9 | 14,832 | 44 (4 regular + 2 of size 2); p0.1 64 | 326 | this run |
| PGL(2,181) | C10, D5n | 592,956 | 6.8 | 2.9 | 873 | 64 (6 regular + 2 of size 2); p0.1 64 | 347 | this run |
| PSL(2,181) × Z2 | D5, twisted D5 | 592,956 | 6.8 | 2.9 | not reduced | 54 (5 regular + 2 of size 2); p0.1 72 | 341 | r1 c2-z2 (min checked here) |
| PSL(2,181) × Z2 | twisted D5, twisted D5 | 592,956 | 6.8 | 6.1 | - | sample only, worse | 444 | r1 c2-z2 |
| A5 × PSL(2,59) | diagonal D5, C10 = ⟨(r,r²),(1,s)⟩ | 615,960 | 9.9 | **0** | not reduced | 111 (11 regular); p0.1 110 | 440 | this run (design), r1 c1-a5 (scan, min checked here) |
| A5 × PSL(2,59) | P4: twisted D5 ⟨(r,r²),(t,t)⟩, same R | 615,960 | 9.9 | 2.6 | not reduced | 95 (uBA 94, uBB 1); p0.1 94 | 431 | r1 c1-a5 |

Disconnected or degenerate, so excluded: L and zRz⁻¹ both inside PSL(2,181) ((C10,C10), (D5s,D5s), (C10,D5s)); any
subgroup containing a central element (SL(2,181), Q × Z_m with H meeting the centre); untwisted pairs in
PSL(2,181) × Z2; A5 × PSL(2,59) pairs where one subgroup has a trivial factor projection. Stabiliser order 20
(PGL(2,229), D10, edge stabiliser C2): 135 members, minimum 704 (r1 c3-wild). Twisted C5 pairs with a central Z_m
(PSL(2,31) × Z200, PSL(2,59) × Z30): minimum 2,564 (c3-wild). |L| ≠ |R| cannot give degree 10 on both sides.
Groups checked for order 5.88–6.2 M with order-10 subgroups whose projections can generate: only PSL(2,229),
PGL(2,181), PSL(2,181) × Z2 and A5 × PSL(2,59) (products of two simple groups otherwise miss the window or have no
element of order 5 in one factor, and a projection of order ≤ 2 gives a disconnected graph).

## Lead (b): what the depth showed

**The evaluator.** In X(G; L, R; D) the A-root BFS is invariant under right multiplication by L, so it can run on
L-orbits (double cosets): about 60k nodes instead of 600k, and the last level runs bottom-up from the few unreached
orbits. cq builds a key → double-coset table once per (G, L, R) (0.3–2 s) and then costs 17–20 ms per A-root BFS.
It reproduced c6b's K scan on 200/200 random classes, and cq2/cq3 reproduce K through their extra factors. This made
every scan below a 20–25 core-minute job, and every question about K a few seconds.

**Special orbits decide the last step.** For K the census of L-orbits on B-vertices is 1 of size 1, 11 of size 2
(cosets in N(C5) = D230), 113 of size 5 (stabiliser C2) and 59,985 regular. An orbit of size s gets about λs/10
independent walk-orbits, so it is missed with probability e^(−λs/10) = 0.41, 0.17, 0.011, 1.3·10⁻⁴; E_s = 3.5. In
median members the special misses are 2–3 times this (4–5 size-2 and 4–5 size-5 orbits), the same factor as the
regular ones. Class 4233 missed exactly two size-2 orbits and nothing else. The general rule: an orbit of B-cosets
under L is special iff some l ∈ L is G-conjugate into R, and its count is governed by |N_G(⟨l⟩)| (≈ q ± 1 in
PSL(2,q)). Simple PSL(2,q) is near-optimal for few specials; central factors (Q × Z_m) multiply them by m.

**Which double cosets could cover the two missing classes.** None, within degree 10. The two missing orbits are
H y with y ∈ N(C5), and with one regular double coset all 10 edges come from HzH; adding a second double coset
raises the degree, and any other z is a different member (the whole family is scanned). Removing the C5-specials
needs L and R whose elements of order 5 are not G-conjugate. That is impossible in PSL/PGL(2,q), where all C5 are
conjugate and contain both classes of order-5 elements. In A5 × PSL(2,59) it works (L = diagonal D5,
R = ⟨(r, r²), (1, s)⟩: (r,r) is not conjugate to (r^j, r^{2j}) because r ≁ r² in both factors). That family has no
special orbits at all, but its regular tail is worse: exact minimum 11 regular orbits.

**The tax is a global correlation.** Median members leave 30–34 regular orbits uncovered against 7.7 expected. Level
counts are tree-like to level 4 and the level-5 loss is close to the birthday count on 60k orbits. Among B-orbits
beyond distance 5, the number of neighbours at distance 6 is overdispersed against Binomial(10, f6): none at all occurs
31 times against 4.7. Tested causes:
- fibres of N(C5): uncovered vertices share a fibre 20–25 times against 3 expected, but 310–340 are alone;
- displacement (some g ∈ Stab(v) moves the root by 2): those orbits are uncovered 7–10 times more often, but they
  explain only 2–3 of 30;
- 4-cycles in the orbit quotient: absent around 96 % of orbits, and most uncovered orbits are among those 96 %.
What remains is not visible at radius ≤ 4. Haar graphs on random S pay 1.5×; one-double-coset families pay
4.4–6.7×, and in every family the bottom of the regular-orbit distribution, not the specials, is what is missing:
K is the only family where any member covered all regular orbits.

**Smarter exact search.** D → aDb⁻¹ (a ∈ N_G(L), b ∈ N_G(R)) is an isomorphism, so families are smaller than their
double-coset counts: (C10, D5n) has 873 distinct graphs, not 59,292. The hands-off count for family C (16,407) used
only conjugation and inversion; with a ≠ b it is at most 8,226. Over all four PSL/PGL(2,q) families there are about
40,000 distinct graphs, and the exact minima are 4, 44, 44, 64.

## Lead (a): what the depth showed

**What an energy-3 state is.** S = {e} ∪ three α-orbits on G = PSL(2,23) × Z97 (α of order 3, |Fix(α)| = 12).
Free orbits of uncovered elements weigh 3 (one per element); with ORBW=3 an uncovered α-fixed element also weighs 3.
The two energy-3 states in handsoff's good_states.tsv have every free orbit covered and miss one fixed element.
An α-fixed element u can only be hit by α-orbits of words whose three members all equal u, so it gets about λ/3
chances; with the measured tax that is e^(−7.5/3) ≈ 0.08 per fixed element, about 0.9 expected misses among the 11
non-identity fixed elements. A descent that covers every free orbit (about 1 in 10⁴, the actual bottleneck) still has
roughly a 60 % chance of leaving a fixed element uncovered. The two energy-3 states are such descents.

**Design instead of annealing?** I looked for a lever and found none:
- Single-orbit replacement: both energy-3 and the cost-6 states are exact local optima over all ~197k orbits
  (earlier sessions, EXDESC). Any change of one orbit changes about 92 % of the length-7 words, so "repairing" one
  fixed element destroys the free coverage.
- Fixed-letter swap (new here, `leadA/f0test.sh`): replacing e by each of the other 11 α-fixed elements gives costs
  42–157 and 36–103 for the two energy-3 states (base 3) and 40–77 for an energy-6 state (base 6). About half of
  all words contain the fixed letter, so this is close to a fresh start.
- Making Fix(α) disappear needs a fixed-point-free automorphism of order 3, which forces G nilpotent (bad mixing,
  STRUCTURE.md §5). The bi-coset trick that removes specials for coset graphs has no Haar analogue at degree 10: an
  affine symmetry s → α(s)c without fixed points has only orbits of size 3, and 10 is not a multiple of 3.
- Inserting vertices (the brief's wording): the Haar graph has 1,177,968 vertices, 1,487 above the target, but one
  uncovered group element u means the pairs (A_x, B_xu) are at distance ≥ 9 for all 588,984 x. No insertion or
  deletion of a few thousand vertices can repair a defect of that size. I did not find any "inserted vertices"
  construction in handsoff-108's files; I read (a) as the energy-3 Haar states named in the brief.

So (a) stays a lottery: P(cost 0) per 50-s F15W3 descent is at most about 1·10⁻⁴ (15,500 earlier descents, none
reached 0). This run added 455 fresh F15W3 descents (4 processes, about 1 h 45 min; 3 on psl 23 x Z97, 1 on prod psl 7 sl 8 x Z7): best chain energy 9 (6 times), no cost 0. Logs: research/d10D8/runs/deep108_g1-4.log.

## The Opus/Haiku split

Spend from tools/session_usage.py (since 22:39:09Z, last line of research/squads/usage/deep-108.jsonl at 01:12):
Opus 1.147 budget units (260k output, 39.4M cache-read tokens, 118 messages), Haiku 0.020 units (292k output,
161 messages): Haiku share 1.7 %. Opus did the thinking and most of the work: the evaluator (cq, cq2, cq3), the K
analysis, the tax tests, the zero-special design, the class reduction and two of the five exhaustive scans. Three
Haikus (one round, 3 cards) ran the A5 × PSL(2,59) and PSL(2,181) × Z2 scans and a wildcard. Their results were
correct (minima rechecked from their scan files), and c2 caught an error in its card (a second D5 class). As in
handsoff-108, most Opus spend is re-reading my own context on each turn (39M cache-read tokens).

## Comparison with the hands-off run on the same cell

- Result: the same (no record). Neither run moved the cell; both leads are now closed for structural reasons, not
  for lack of CPU.
- Depth: handsoff-108 found K and scanned it (min 4). This run explained the 4 (two size-2 special orbits, coin flip
  P about 3 %) and the 4.4x tax (non-local correlation of neighbour coverage, with three local causes ruled out). It
  closed every other order-10 family near the bound (three new exhaustive families, two by Haikus) and showed
  that the families are smaller than counted (normaliser reduction: C 8,226 classes, not 16,407). It designed a
  family with no special orbits (A5 × PSL(2,59)), which turned out worse. For (a) it found no design lever and
  explained why: fixed-element misses are e^(-λ/3) events, not repairable locally.
- Breadth: handsoff covered more directions (20 Haiku runs: hexagon lifts, group screens, schedule A/B tests).
  This run covered fewer directions, each to an exact answer.
- Spend: handsoff 0.80 Opus + 0.29 Haiku over 5 h 50 min; this run 1.15 Opus + 0.02 Haiku over 2 h 34 min. Opus-led
  depth costs about 3x more Opus per hour. Per closed question it is cheaper, because the evaluator made each family
  a 20-minute exact scan instead of a sampling estimate.
- Left open: the global mechanism of the tax (radius > 4 correlation); the Haar grind (lead a) at about 1e-4 per
  descent or less, which only volume can test.

## Files

`NOTES.md` (running notes with every number), `cq/cq.c` (PSL/PGL(2,q)), `cq/cq2.c` (× Z_m), `cq/cq3.c` (A × PSL(2,p)),
`scans/` (exhaustive scans, one line per member), `a5/gens.py`, `leadA/f0test.sh` and its output, `r1/` (squad round
1: cards, scoreboard, worker folders), `ref/` (handsoff code and K scan used for validation). Grind logs in
`research/d10D8/runs/deep108_g*.log`. Spend: `research/squads/usage/deep-108.jsonl`.
