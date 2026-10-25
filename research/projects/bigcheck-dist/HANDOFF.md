# bigcheck-dist: handoff

Opus lead session, 2026-10-25, branch claude/bigcheck-dist-h6r1g3. Read README.md first (the checker).

## Done
- **bcd.c + bcd_merge.py** (README.md): checker for explicit graphs and cyclic voltage lifts, verified automorphisms,
  orbit representatives, parts i/K with certificates, merge. `--cost` mode for searches. Tested against apsp.c on
  random lifts and Haar graphs, against apsp_orb.c on the coordinator's (14,7) 1,774,584 graph (4 parts, VALID,
  checks/d14D7_n1774584/).
- Survey of the big D = 8..10 cells we do not hold: (10,8) 1,176,480, (12,8) 4,650,100, (14,8) 14,172,480,
  (16,8) 36,201,060 decode exactly as 30, 35, 40, 45 copies of H(q), q = 7, 9, 11, 13, Δ = q+3: the table value is
  5·⌊(q+5)/2⌋·|H(q)| (and (13,8) = 15·|H(11)| at Δ = q+2). The survey (DS14v2 §3.4.5) credits Delorme's 1985 bipartite
  ∗-product/compounding constructions; the paper (JGT 9, 325-334) is not open access and its D = 8 definition is
  unknown to us. (15,10) and (16,10) already have cloud-checked Haar graphs on other branches
  (claude/bipartite-d15-d10-search-h3rdep: 2,467,618,800; claude/bipartite-16-10-cell-kras4l: 4,220,872,800),
  not yet recorded.
- d8/: tools for cyclic lifts of H(q) + 2 extra edges per vertex, with the Singer torus of SL(3,q) ⊂ G2(q) as symmetry
  (singer.py; free of order 13, 31, 19, 133 for q = 3, 5, 7, 11): x2s.c (annealer; C copies, r bijections), x2d.c
  (same with ±1 multipliers), nbw.c / nbwx.c (reduced-walk counts), hexspec.py (bcd specs from Python).

## Findings so far (D = 8, q = 5, Δ = 8; Delorme's construction has M = 25 copies; M ≥ 31 would be an (8,8) record)
- Random τ-invariant voltages: cost (pairs at distance > 8 over the 252 orbit sources) ≈ 8, 70, 1270, 7800 at
  M = 16, 20, 25, 31. Annealing: M = 16 solved, M = 20 stuck at cost 2, M = 25 stuck near 580.
- Failures sit at point-line pairs at base distance 1, 3, 5 (mostly 5).
- Reduced walks of length ≤ 7 between point-line pairs: min ≈ 155-200 in the plain cyclic lift (C = 1), so counting
  does not forbid M ≈ 30; in the 5-copy product family (Z_5 × Z_k) only 11-16 per class at distance 1, 3 (k ≲ 11).
- A provable family (Δ = q+2, q+3 copies, "rainbow" point colourings) exists on paper but is weaker than Delorme's q+4.
- Squad round bcd-d8-r1 (research/squads/bcd-d8-r1/): best valid M = 17 (c7); algebraic incidence voltages, extra
  Frobenius symmetry (impossible: it fixes points but no lines), point-point jumps, GA, product structure all no better
  than plain annealing.

## Running / next
- /tmp/hs: haar_sym orbit search for (10,8) on PSL(2,23) × Z97 (N = 588,984 > 588,240 needed), seed 11, 3 h, 1 thread
  (an earlier 34-min run reached cost 12; STRUCTURE.md estimates ~2·10⁷ evaluations).
- Open: a structured (algebraic) voltage design for D = 8 hexagon lifts; reconstruct Delorme's 5⌊(q+5)/2⌋ family, then
  try hub surgery as at D = 7.
