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

- bcd lift mode also takes SL(2,p) × Z_n and PSL(2,p) × Z_n voltages (Haar graphs = lifts of the dipole,
  haar2lift.py); tested on four records and a perturbed graph; 10 s for (11,9) 16.8 M on one thread.
- Prior work found later: the cell-10-8 session (Oct 24, claude/cell-10-8-search-t6pwvg) covered the D = 8 decoding,
  a Z10 lemma (10 copies free), the guaranteed-walk count and Haar runs; credited in d8/NOTES.md.

## Parallel work on this project
The coordinator also gave this project to a Haiku worker (master commit 4b54aa07, branch
claude/bigcheck-dist-haiku-2iqw1y): apsp_shard.c, a sharded all-pairs checker for explicit edge lists with the level
shift, with its own tests and HANDOFF.md. Its "next steps" (implicit level covers, single-source bitsets) are covered
by bcd (lift mode, -DWB=1). The two checkers agree on its test graphs (README §4). Both branches add
research/projects/bigcheck-dist/HANDOFF.md, so a merge needs the two handoffs combined.

## Running / next
- /tmp/hs/runs: (10,8) Haar orbit search on PSL(2,7) × SL(2,8) × Z7 (N = 592,704; cell-10-8's better group), seeds
  21, 22 (RESTART=1) and 23 (haar_sym2 RESTARTAFTER=2 ORBW=3), ~2.7 h each, started 06:00 UTC. Earlier PSL(2,23) × Z97
  seeds 11-13 stopped at best 12, 9, 10. Request for more cloud seeds: research/squads/requests/2026-10-25T0550-d10D8-haar.md.
- An Opus agent works on reconstructing/beating Delorme's 5⌊(q+5)/2⌋ (output: d8/theory/NOTES.md).
- /tmp/bcdt/big: independent bcd checks (SL lift mode, 1 thread each) of the two unrecorded D = 10 Haar candidates:
  (15,10) 2,467,618,800 (SL(2,149) × Z373, branch claude/bipartite-d15-d10-search-h3rdep, sha256 6430a3a4…, WB=8,
  7.4 GB) and (16,10) 4,386,127,200 (SL(2,151) × Z637, branch claude/bipartite-16-10-cell-kras4l, sha256 f2a70a0d…,
  WB=1, 1.6 GB; so far checked only by that session's hcheck5). Results go to checks/ when done.
- Open: a structured (algebraic) voltage design for D = 8 hexagon lifts; reconstruct Delorme's 5⌊(q+5)/2⌋ family, then
  try hub surgery as at D = 7.
