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
1. **n = 588 / 589** (7,056 / 7,068). Starts: K33 block (3 new points all on 3 new lines, kkk.py K=3) 648-776 at
   n = 588; two K22 blocks (k22x.py 2) 1,146-1,550 and one K44 block (kkk.py K=4) 1,240 at n = 589. The GREEDY mode
   of research/d11D5/dc/po7R.c (steepest descent over sigma swaps at the new vertices) takes ~100 off a start.
   Anneals of these were running at the end of this session (see the cell notes for where they stopped).
2. For several blocks under one C: a "parabolic" C keeps exactly the W-lines meeting an axis isotropic, i.e. the
   points R with C(delta(R)) isotropic form a plane P0^perp; up to 8 hyperbolic lines through one point R0 of it are
   disjoint off R0 (k22p.py). One block starts at 310 that way, but two blocks through one R0 interact (1,550).
3. Other cells: delta o C needs a duality of W(q), so q even (W(q) is self-dual exactly for q even; a polarity for
   odd powers of 2). The K22 + delta o C recipe should transfer to W(4) ((7,5)) and W(16) ((19,5)) as written, with
   a duality in place of the polarity. For odd q (W(7) -> (10,5), W(9) -> (12,5), W(11) -> (14,5)) there is no
   duality of W(q); the one-pair recipe of round 3 still applies there.
