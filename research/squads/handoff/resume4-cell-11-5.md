# Handoff: job resume4-cell-11-5 (round 4 of cell-11-5), Oct 25-26 2026

Session session_01YVUXzZUE2Fjy42D4zug9Gh. Branches: claude/cell-11-5-bipartite-search-lyemfs (draft PR #388, as the
brief asked) and the session's own claude/cell-11-5-bipartite-search-7d5bhg (draft PR #395, same commits).

## Result
- **(11,5) ≥ 7,044** (was 7,032 from round 3, not yet recorded; recorded 7,020): DM Z6 lift of W(8) plus a K22
  switch (two point-line pairs). research/d11D5/graphs/d11D5_n7044_CHECK.md: apsp.c VALID, diameter exactly 5,
  11-regular, bipartite, 38,742 edges, sha256 125fb687...; an independent numpy bit-parallel BFS
  (research/d11D5/dc/bitcheck.py) agrees. Needs the coordinator's check.

## How
1. sigma = delta o C (research/d11D5/dc/README.md, NOTES.md "Round 4"): the polarity after a non-symplectic
   collineation; every pencil's sigma-preimage is a PG-line (a covering set), so a switched base fails only near the
   switch. Starts: one pair 236-310, two pairs ~400-600 (earlier 2,000-5,000).
2. K22 switch (squad r5 card c8): new points x*, y* both on new lines l*, m*; x* on 7 old lines delta(R), R on a
   hyperbolic line h1 (minus two points), y* on 7 from h2; the 14 removed points split 7/7 onto l*, m*; sigma =
   delta o C except sigma(C^-1(Ra)) = l*, sigma(x*) = delta(Ra) (and the same for y*, m*). Builder:
   research/squads/r5-d11D5/c8/k22.py; generalised (several blocks, K_kk blocks): research/d11D5/dc/k22x.py, kkk.py.
3. po7 anneal (T0 2 -> 0.15): 414 -> 18; cold po7 (T0 0.6 -> 0.08): 12; wpo with **LMAX=3000 DECAY=10** (the
   default LMAX 500 drifts up from 12-18): 8, 2, 0; nujoint TARGET=1 from a random nu: 0 in 89 s (seed 2; seed 1 was
   at 2 when stopped); finish.sh; bitcheck.py. The pipeline is research/d11D5/dc/chain.sh (wpo, nujoint, finish).

## Open (in order)
1. **n = 588 (7,056).** Best structural cost **52**: the 6-cycle block (X_j on N_j, N_{j+1}) with all three
   hyperbolic lines through one point R0 of the plane S of a parabolic C (`PLANE=1 PAT="0-0,0-1,1-1,1-2,2-2,2-0"
   kkk.py`, squad r6 card c8): start 622 -> po7 152 -> cold 70 -> 60 -> evolutionary cold cycles (dc/evo.sh) 52, where it stalls (T0 0.3-1.8). Four more lineages of the same design ended at 114-140 (1,800 s) and ~105 after cold cycles.
   File research/d11D5/dc/n588_c6plane_best.in (see the cell notes for the last value). wpo (LMAX 3000-10000) does not
   help above ~20, and the step from 52 to ~20 is what is missing. Other n = 588 designs, all worse: K33 starts
   622-776 -> 148-168 after 1,800 s; triangle with full point-side pencils (dc/tri.py) 638 -> 120; 17 incidence
   patterns (squad r6 c1) 682-1,092 at the start; a third pair grown on the solved 7,044 base 1,594 -> 532.
   n = 589: two K22 blocks 1,146 -> 772, cube Q3 1,180 -> 850.
   Ideas not tried: (a) a faster, incremental cost evaluation (po7 recomputes all 1,176 sources per move, ~700
   moves/s; the n = 588 lineage got 152 -> 52 in ~1.5 CPU hours and then stalled even with T0 up to 1.8); (b) blocks
   whose LINE side is the structured one (moved points on hyperbolic lines, squad r5 c5) and whose point side is
   annealed, or mixed per vertex like the 7,044 K22 (x* full pencil, y* 8 of 9). Tried at the end and worse: a K22
   plus a pendant third pair with all hyperbolic lines through one point of the plane (kkk.py PLANE=1, patterns
   "0-0,0-1,1-0,1-1,2-1,2-2" and "...,2-0,2-1,2-2"): starts 950-1,000.
2. For several blocks under one C: a "parabolic" C keeps exactly the W-lines meeting an axis isotropic, i.e. the
   points R with C(delta(R)) isotropic form a plane P0^perp; up to 8 hyperbolic lines through one point R0 of it are
   disjoint off R0 (k22p.py). One block starts at 310 that way, but two blocks through one R0 interact (1,550).
3. Other cells: delta o C needs a bijection lines -> points of W(q) taking pencils to PG-lines, i.e. a duality of
   W(q); that exists only for q even (for odd q, Q(4,q) has no full embedding in PG(3,q)). So it does not transfer to
   the odd-q side results (10,5) W(7), (12,5) W(9), (14,5) W(11). For even q it would apply to W(4) at (7,5), but the DM
   lift there is 12 * 85 = 1,020, below the lab's 1,152; W(16) is degree 19, outside the table.
