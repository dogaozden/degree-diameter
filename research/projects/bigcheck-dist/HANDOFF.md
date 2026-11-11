# bigcheck-dist: handoff

Read BRIEF.md first. No earlier session left a HANDOFF or a claude/bigcheck-dist branch; this work starts from the brief.
Branch: `claude/bigcheck-dist-haiku-2iqw1y` (the harness's designated branch; the brief's name was `claude/bigcheck-dist-haiku`).

## Done (step 1 of the brief: sharded verifier)

- `apsp_shard.c`: the all-pairs check of apsp.c / apsp_orb.c split into shards.
  - `apsp_shard shard EDGES d D K I T full|L,B > report_I.txt` runs the 64-source batches b with b % K == I (T threads)
    and prints one line per batch with its largest eccentricity, plus the structural checks.
  - `apsp_shard merge EDGES d D K full|L,B report_0 ... report_{K-1}` rereads the edge file (n, m, and an order-independent
    fingerprint), then accepts only a complete, consistent set. It rejects a missing, repeated, truncated or foreign report,
    a parameter or structure mismatch, or a batch line that is not the one its shard owns. It prints `RESULT VALID|INVALID`.
  - Layout `L,B` (level cover): the shift v -> (v+B) mod LB is checked edge by edge as an automorphism, and the sources
    are [0,B) plus the hubs. Eccentricity is constant on shift orbits and every orbit meets [0,B), so the largest eccentricity over
    those sources is the diameter.
- `level_graph.py`: test level covers, with (l,p) ~ (l+1 mod L, p+s) for offsets s. Bipartite iff L is even.
- `run_tests.sh [WORKDIR]`: builds apsp.c and apsp_shard.c, then checks (last run: ALL PASS, 27 checks):
  - every sharded verdict and diameter matches apsp.c on a Haar graph (d4D10, diameter 10) and on level covers, with
    full and L,B layouts, K from 2 to 5 (K above the batch count gives empty shards), and D = diameter (VALID) and D-1 (INVALID);
  - 1-thread and 3-thread reports are byte-identical;
  - odd L (not bipartite) and offsets {0} (disconnected) are refused; a wrong level size is refused;
  - merge refuses truncated, foreign, repeated, missing and layout-mismatched reports.

## Measured (4-core cloud box)

- lvl20 (L=20, B=5000, offsets 0,1: n=100,000, m=200,000, degree 4, diameter 2510):
  one shard with 4 threads: 17.4 s wall, 67 CPU-s over 79 batches, about 0.85 CPU-s per batch. Four 1-thread shards run in parallel
  take 17.5 s wall; merge gives `diameter 2510`, `RESULT INVALID` at D=99 as it should.
- Cost model: a batch costs about n x (BFS levels, which is the eccentricity) x degree word operations. Level covers with
  big diameter are therefore expensive even with orbit reduction.
- Memory (estimate from the code, not measured): about 24n bytes per thread (vis, fr, nx as uint64 per vertex), plus the CSR
  (8n + 16m bytes) and the edge arrays read from the file (16 bytes per edge). The file route tops out at tens of millions
  of vertices, as the brief says.
- Reference cross-check for lvl20: `apsp_mt` (4 threads, no symmetry, all 100,000 sources) gives diameter 2510 and
  `RESULT INVALID` at D=99, matching the sharded merge.

## Trust limits

- A merge certifies the reports, not the arithmetic. A tampered batch line that lowers an eccentricity still passes merge.
  Reports are deterministic (no timing, no thread count in them), so the coordinator must rerun a sample of shards and diff
  them byte for byte. The test suite does this for T=1 vs T=3.
- Hubs: sources include the hubs, but no test graph has hubs; a shift-invariant bipartite hub construction was not found.

## Next steps (for the next session)

1. Implicit level-cover mode: compute neighbours from the vertex index with the offset rule, so no edge file or CSR is needed.
   Memory is then about 24n bytes per thread. Check that it agrees with the explicit mode on every graph in run_tests.sh.
2. For large n with few sources, a single-source bitset BFS (about 3n/8 bytes) if B is small.
3. Brief step 3: search the big D = 8..10 cells for constructions these checkers can verify (lifts with large groups,
   hexagon/octagon covers). Verify each record with apsp.c, or with the sharded merge, before claiming it.
4. Do not edit records, README or RESULTS.md (brief).
