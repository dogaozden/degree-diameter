# sigma = delta o C (job resume4-cell-11-5, Oct 25-26)

Structured sigma for the doubled-matching (DM) bases: sigma(s) = delta(C(s)) with delta the polarity of W(8) and C a
collineation of PG(3,8) outside PGammaSp(4,8).  Then sigma^-1 of every pencil is a PG-line of PG(3,8), and every PG-line
is a covering set of W(8) (each point is collinear with one of its points), so route (b) of the coset +1 condition
holds everywhere, independently of route (a).  On W(8) itself it scores 0 for every C tried.  On a switched base all
remaining failures are local to the switch (x*, l*, the switch lines L_i and the moved points p_i).

- gq.py: W(8) coordinates, polarity, collineations.
- dsig.py base seed out: replace sigma of a base by delta o C (random C).
- mkdc.py K seed out: 9-flag regulus switch(es) (L_i = delta(R_i), R_i on a hyperbolic line h) with C(L_i) in W and
  p_i chosen with C^-1(delta(p_i)) in W, so every coset-0 demand of the switch is met.
- mkdc2.py seed out [KS]: incident version (8 lines of the regulus; the omitted point R_9 gives sigma(C^-1(R_9)) = l*
  and sigma(x*) = delta(R_9)), so sigma^-1 of the pencil of x* is the PG-line C^-1(h).  KS = 2 puts the second h in the
  plane delta(axis)^perp so that one C serves both switches.
- miss.py (point-line pairs at distance >= 5 per vertex), tagf.py (failure classes by vertex role).

Start costs (po7 structural cost): one pair, spread switch: sigma = delta 2,496, random sigma ~2,300, delta o C ~800;
mkdc.py 426-602; mkdc2.py 236-302.  Two pairs: sigma = delta 5,022, random ~4,600, delta o C ~1,700, mkdc2.py KS=2
604-1,026 (earlier sessions' two-pair starts: ~2,000 and up).

## Later tools (same session)

- `po7R.c`: po7 + REF/LAM penalty, LOCAL (sigma swaps must touch a listed point), GREEDY=585 (steepest descent over
  sigma swaps at the new vertices and their sigma partners, then exit).
- `chain.sh base.in prefix seed`: wpo (if cost > 0) -> nujoint TARGET=1 from a random nu -> inc/finish.sh (z6 lift,
  edge list, apsp). `bitcheck.py edges`: independent numpy check (simple, regular, bipartite, diameter).
- `k22x.py KK seed out tries`: KK K22 blocks (squad r5 c8's design, generalised). `k22p.py`: K22 blocks with all
  hyperbolic lines through one point R0 of the plane S of a parabolic C. `kkk.py`: any block (env K, CYC=1, PLANE=1,
  PAT="i-j,..." for any incidence pattern between new points and new lines). `tri.py`: cycle block whose hyperbolic
  lines form a polygon in S (every new point's pencil preimage is a full PG-line); `tri2.py`: also forces moved points
  for the new lines (worse).
- `evo.sh start prefix gens`: generations of 4 cold po7 anneals (T0 list in env TS) from the current best; wpo when
  <= 20. `flagnew.py`: exhaustive flag swaps between new lines and switch lines (all cost +120 or more at n = 588).
- Bases: `n587_k22_struct0.in` (structural 0, the 7,044 base before the nu stage), `n588_c6plane_best.in` (n = 588,
  structural cost 52), `n588_k33_start*.in`, `e2_*.in` (two incident regulus switches).
