# d10D5 squad round 2 (cell (10,5); record 4,820 verified, 4,832 = 8 flags expected soon)

Read research/squads/d10D5/r1/README.md first (the construction, rules, pipeline). What changed since round 1:

1. **Coset-0 is solved by a targeted route move.** For two opposite points v, u the only coset-0 "route" of length 4
   is v -> sigma(v) -> y -> sigma(u) -> u, so it exists iff sigma(v) and sigma(u) meet (dually for lines:
   sigma^-1 of the two lines collinear). dmfast_hub now has PTARG=0.5: half the nu flips are on geodesics of a bad
   pair, and half the sigma swaps make a bad pair's sigma-lines meet. On c5's 8-flag set this took the cost from 8
   to 1 in 45 s (all the round-1 runs had stalled at 5..29 without it).
2. **Relaxed coverage with patches.** dmfast_hub RELAX=1 PATCH=1 accepts any sigma swap that keeps every freed
   point/line covered by some length-4 route (not only the exact matching), where targets lying on a freed line (or
   lines through a freed point) count as covered because a hub edge patches them. So exact-matching sets are NOT
   needed any more: start from an exact set and add flags; dmhub COVIT=... CT0=0.25 (fast coverage annealing with
   targeted moves) usually brings a new flag's coverage cost from ~190 to 0..2 in a minute. FORCE="p:l ..." in dmhub
   forces sigma(p) = l (to make new flags).
3. **Hub graph rule.** A hub edge z_i ~ z'_m (line-side hub of flag i to a point-side hub of flag m) puts z_i within 4
   of both line-side hubs of m (z_i - z'_m - (l_m,h) - (p_m,h') - z_m, since p_m is on l_m), and z'_m within 4 of both
   point-side hubs of i. So 2 edges per pair of flags suffice, and each hub has 4 spare edges: with all freed points
   pairwise opposite this is a tournament with out/in-degree <= 4, so k <= 9 flags fit with 2 hubs per side. Collinear
   freed points (concurrent freed lines) need nothing on that side. dmhub builds the hub graph with this rule plus the
   patch edges (HGIT = iterations); "hub src 0" in its output means all hub-sourced pairs are fine.
4. Pipeline now: (flags + sigma) -> `dmfast_hub` with FREE, RELAX=1 PATCH=1 PTARG=0.5 SWAPP=0.01 (coset-0, keeps
   coverage) -> `dmhub ITERS=0 HGIT=3000000` (hubs, hub graph, exact BFS cost) -> apsp. Convert dmhub .sol files back
   to the lift2 format with `python3 sol2lift2.py IN.sol OUT.sol` (prints the freed points).
   Round-1 data: c5 (k=8 orbit: ../r1/c5/k8.sol.free, k8b.sol), c8 (k=7 triad sampler: ../r1/c8/), c1 (fast flag SA in
   C: ../r1/c1/flagls.c).

Tools: research/squads/d10D5/hubs/ (copy into your card folder: *.c *.py; build as in r1/README.md).
Scoreboard: research/squads/d10D5/r2/scoreboard.jsonl, same JSON line format. Same machine rules (one heavy process,
`timeout 900 nice -n 10`, THREADS=1, no commits, only your card folder r2/<card>/).
