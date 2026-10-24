# Round d11D10-r1 cards (2026-10-24, Opus session cell-11-10)

Shared rules, tools, scorer and scoreboard format: PREAMBLE.md. Squad A = search cards (heavy budget 15 slot-min each).
Squad B = tools and analysis cards (light budget, 3 slot-min unless stated). Several A cards share groups on purpose,
so k = 3 and k = 5 meet head to head on the same group.

## Squad A (search)

- **A1: k = 5 on PSL(2,p) × Z_n with small p and a large cyclic factor.** Groups: psl 41 × Z2161 (148.8M, μ 24.4),
  psl 61 × Z661 (150.0M, μ 27.6), psl 41 × Z2201 (151.6M, μ 32.6). First `RANDORB=30` on each (ORBIT="5 2 1"), then
  anneal (ORBIT="5 2 1" ORBW=5) the most promising one for up to 600 s; if solved, step to the next larger one.
  Question to answer: does a large cyclic factor (n ≈ 700–2,200) hurt at D = 10?
- **A2: k = 5 on PSL(2,p) × Z_n with medium p.** Groups: psl 89 × Z211 (148.7M, μ 24.1), psl 71 × Z421 (150.65M,
  μ 29.6), psl 79 × Z311 (153.3M, μ 38.9). Same plan as A1 (RANDORB=30 each, then ORBW=5 anneal ≤ 600 s, step up if solved).
- **A3: k = 5 on SL(2,p) × Z_n.** Groups: sl 61 × Z331 (150.2M, μ 28.3), sl 41 × Z1091 (150.3M, μ 28.5),
  sl 71 × Z211 (151.0M, μ 30.7). SL has twice the fixed points of PSL; does it still compete? Same plan as A1.
- **A4: k = 3 (ORBIT="3 3 2") on PSL(2,p) × Z_n, head to head with A1/A2.** Groups: psl 61 × Z661 (150.0M, μ 27.6;
  same group as A1), psl 71 × Z421 (150.65M, μ 29.6; same as A2), psl 127 × Z73 (149.5M, μ 26.3). RANDORB=30 each,
  then anneal the best ≤ 600 s (no ORBW), step up if solved.
- **A5: k = 3 on SL(2,p) × Z_n, head to head with A3.** Groups: sl 61 × Z331 (150.2M, μ 28.3; same as A3),
  sl 73 × Z193 (150.1M, μ 28.0), sl 101 × Z73 (150.4M, μ 28.8). Same plan as A4.
- **A6: the choice of α.** Group psl 71 × Z421 (μ 29.6), ORBIT="5 2 1". α = conjugation by g (order 5) times z ↦ rz.
  The pairing matters: AR = r, r², r³, r⁴ give four different automorphism groups. Find the default r and the ALPHA
  index in the log line `alpha: conj by mat(...) (index I), z -> r z`, then RANDORB=30 for each AR in {r, r², r³, r⁴}
  (mod 421) and for two other ALPHA choices if you can find conjugating elements of order 5 (ALPHA = an index of an
  element of order 5; the log prints the default one). Anneal the best pairing ≤ 600 s with ORBW=5.
- **A7: Frobenius α (wildcard).** haar_sym's `AFROB=j` uses the field automorphism x ↦ x^(p^j) of GF(p^e) on matrix
  entries (order e/gcd(e,j)) instead of conjugation. Order 5 needs e = 5: `sl 32` (= PSL(2,32), Fix = SL(2,2), only 6
  elements) × Z_n with every prime of n ≡ 1 mod 5 (e.g. n = 2311 gives 151.3M vertices), or `psl 243` × Z11
  (157.8M, μ ≈ 60, too hard) / smaller. RANDORB=30 on two groups near 150M, compare with A1–A3's RANDORB numbers,
  anneal the better one ≤ 600 s with ORBW=5. There is no low-memory checker for prime powers yet (card B2 writes one),
  so report haar_sym's own full-check verdict and mark valid=false unless B2's checker is ready in
  `research/squads/d11D10-r1/B2/`.
- **A8: wildcard.** Find an approach none of the other cards uses, within haar_sym's options or a small change of
  your own (copy the source into your folder). Other cards: A1–A3 k = 5 conjugation on PSL/SL × Z_n with ORBW = 5,
  A4–A5 k = 3 on the same groups, A6 α pairings (AR/ALPHA), A7 Frobenius α, B1–B3 new checkers, B4 ball-growth census,
  B5 speed knobs, B6 better orbit moves, B7 theory, B8 open wildcard. Examples, not instructions: K = 16 or 4,
  TARGP 30 or 100, COOL/REHEAT schedules, RESTART=1, product groups (`prod psl 11 psl 59` style specs, see haar_sym.c
  usage), or `ORBIT="11 1 0"`. Report what you tried and the lowest cost at a stated μ.

## Squad B (tools and analysis)

- **B1: a second independent checker for PSL(2,p) × Z_n.** Write it from scratch in C in your folder (do not copy
  `research/structured/tools/haarcheck_psl.c`; use a different element encoding, e.g. normalise the matrix so its
  first nonzero entry is in 1..(p−1)/2, or work with the action on the projective line). Graph: vertices (g,A),
  (g,B), edges (g,A) ~ (s·g, B); BFS from (e,A) and from (e,B) over bitsets gives the exact diameter (right
  multiplication is transitive on each side). Validate: it must agree with haarcheck_psl on the small PSL solutions
  in `research/frontier/sols/` (pick 3 with < 2M vertices, also checkable by build_haar2.py), and reject two corrupted
  copies (one generator changed; one repeated generator). Then check
  `research/frontier/sols/d11D10_psl_149_43_orb3_s1.txt` (142,235,400 vertices) through the gate. Budget 6 slot-min.
- **B2: a low-memory checker for SL(2,q) and PSL(2,q) × Z_n with q = p^e, e ≥ 2.** Same graph and BFS as B1. The
  field is GF(p)[x]/(f) with f the polynomial in the solution header ("poly x^…"); matrix entries are written as
  integers Σ c_i p^i (see haar_sym.c, "finite fields", and research/frontier/build_haar2.py for the exact format).
  Validate against build_haar2.py on 3 small solutions you make yourself with haar_sym (e.g. `sl 9`, `psl 25`,
  `sl 32` at small D, < 2M vertices) and on a corrupted copy. Leave the binary as `B2/haarcheck_pq` with a README line.
  Budget 5 slot-min.
- **B3: a low-memory checker for PGL(2,p) × Z_n.** Same as B2 for the `pgl p` family (p an odd prime). Learn the
  element encoding from haar_sym.c and build_haar2.py. Validate on 3 small solutions you make (< 2M vertices) against
  build_haar2.py and on a corrupted copy. Budget 4 slot-min.
- **B4: ball-growth census.** For every group named in A1–A5 and A7 (and 6 more from candidates_k5.txt between 148M
  and 156M), run `RANDORB=3 LEVELS=3` with the card's ORBIT and record the number of distinct elements per BFS level
  (levels 1–8) against the non-backtracking count 11·10^(L−1). Rank the groups by the loss at levels 7–8. Hypothesis
  to test: large cyclic factors and SL (vs PSL) lose more words. Budget 4 slot-min. Report a table in B4/census.md.
- **B5: speed knobs.** On psl 101 × Z151 (k = 5) and sl 79 × Z151 (k = 3), compare evaluations per second for
  FAST=1 vs FAST=2, HWMIN/HWMAX (wide-row subgroup range), PFD (prefetch distance) using `BENCH=m` or short
  `MAXSTEPS` runs (see the top of haar_sym.c and research/structured/haar_fast.c). Confirm that the faster setting
  gives identical costs (`TRACE=1 VCLOCK=0.01 MAXSTEPS=200` hash must match). Budget 4 slot-min. Report the best
  setting and its speedup.
- **B6: better orbit moves.** Read `orbit_main` and `targeted()` in haar_sym.c. Write a variant (copy the source to
  B6/haar_sym_b6.c) whose candidate orbits are chosen to cover a currently uncovered element with a short word, or
  any other idea that makes the annealer need fewer evaluations. Test at small scale on the old (11,8) cell:
  `ORBIT="5 2 1" ORBW=5 ... 11 8 SECS SEED 8 OUT psl 59 11` (N = 1.13M, μ = 60, a few ms per evaluation) against the
  unchanged haar_sym with the same seeds and time. Budget 10 slot-min.
- **B7: theory and planning.** Read `git show origin/claude/cd-theory-beyond-random-3ybyf2:research/theory/BEYOND_RANDOM.md`
  (§1–§3) and research/structured/tools/plan_orbit.py. Compute μ_A (the clumped-Poisson mean) carefully for k = 3 and
  k = 5 candidates with N between 76M and 80M, including Frobenius α on SL(2,32) × Z_n and PSL(2,243) × Z_n, and
  predict the largest graph each family should reach with 4 single-thread core-hours using the effort law
  evals ≈ 10⁵·e^((μ_A−13)/2) and the measured 0.25 s (k = 5) / 0.09 s (k = 3) per evaluation. Write B7/plan.md
  with a ranked table of the 10 best runs to do. No heavy runs (budget 0; light Python only).
- **B8: wildcard.** Find an approach to (11,10) that none of the other cards uses. Other cards: A1–A3 k = 5
  conjugation on PSL/SL × Z_n, A4–A5 k = 3, A6 α pairings, A7 Frobenius α, A8 open search wildcard, B1–B3 checkers,
  B4 ball-growth census, B5 speed knobs, B6 better orbit moves, B7 theory. It can be a different construction
  (voltage lifts, products, other group families), a smarter use of the existing tools, or an analysis. Budget
  5 slot-min. Report a concrete result, even a negative one.
