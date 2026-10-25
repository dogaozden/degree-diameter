# d10D5 squad round 3 (cell (10,5); record 4,836 = 9 freed flags, verified)

Read research/squads/d10D5/r1/README.md and r2/README.md first. Goal now: **10 freed flags (4,840)** or more.

State of the art (Opus, after round 2):
- Hub graph is no longer a limit: same-side hubs need distance <= 4, and paths of length 4 inside the hub graph count
  (dmhub HGDIST=1). Hub edges also give coverage routes ((p_i,0) -> z_i -> z'_j -> (l_j) -> points of l_j; dually).
- `dmhub HGFIRST=1 HGDIST=1 HGFILL=1 PHUB=0.1 HW=2 COVIT=999999999 CSECS=<seconds> CT0=0.25` builds a hub graph first,
  then anneals sigma and hub edges jointly against coverage (hub routes counted). `HUBG_IN=<dmhub .sol>` reuses that
  file's hub graph (with HGFIRST=1 the joint annealing continues from it). `REPAIR=1 BEAM=300 RDEPTH=10` runs a beam
  search of targeted swaps after the coverage phase. "cover cost final 0" is what we need; then:
  `python3 sol2lift2.py X.sol X_l2.sol`, coset-0: `dmfast_hub` with `FREE=... RELAX=1 HUBADJ="i:j ..." PTARG=0.5
  SWAPP=0.01 ITERS=30000000 TEMP0=0.25 TEMP1=0.02` (HUBADJ = the flag-level pairs (a/H):(b/H) of the hubgraph line of
  X.sol), then a hot polish from its OUT with PTARG=1.0 TEMP0=0.5 TEMP1=0.05 SWAPP=0.05 ITERS=3000000 if it stalls
  at 1-3; finally `dmhub HUBG_IN=X.sol ITERS=0` on the coset-0 solution and `./apsp out.edges 10 5`.
- 9 flags: 266:64 41:289 225:350 65:202 263:330 283:130 398:292 253:247 19:139 (states/k9_valid*): VALID 4,836.
- 10 flags: adding 100:366 or 38:272 to those 9 reaches coverage cost 1 (states/k10_orbit_100*, k10_orbit_38*: dmhub
  .sol with the hub graph, lift2 sigma, .free), but 20+ minutes of joint annealing and a beam repair (300 x 10) stay
  at 1. The hole is for freed point 65 (index 3), which is collinear with three other freed points (crowded).
  Another family (round-2 card c3's valid 7-flag set + 291:47 172:301) takes 8 flags in minutes and stalls at 1-2
  holes for 9.
