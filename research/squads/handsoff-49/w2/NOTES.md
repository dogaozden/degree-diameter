# w2 NOTES: metacyclic Haar sweep, orders 2,486..2,600

Start: 2026-10-31 21:41 UTC. Planned end: 23:41 UTC.

## Setup
- `enum_groups.py LO HI` lists meta groups Z_m x|_r Z_k with m*k in [LO,HI], one r per cyclic subgroup <r> of units
  with r^k = 1 (r != 1). 1,779 groups for 2486..2600. `groups_all.txt` (N m k r), `groups_ab.txt` (+ |G/G'| = k*gcd(m,r-1)).
- Screen set A (k >= 3, |G/G'| <= 200): 937 groups, `screen_A.txt`, sorted by |G/G'|. Screen set B (k >= 3, |G/G'| > 200,
  582 groups) and the k <= 2 groups (dihedral-like, pilot cost 3000+) are left for later.
- `screen.sh LIST SECS SEED OUT.tsv`: haar_tab 4 9 SECS SEED K=8, one run per group, appends `N m k r ab best time`.
- `deepen.sh LIST SECS SEEDS...`: same with several seeds, appends to `deep.tsv`; a cost-0 run is logged in `cost0.txt`.

## Calibration
- haar_tab finds cost 0 for meta 71 35 49 (N=2485) in 3.7 s. Two seconds reproduce the known floors: meta 71 35 49 -> 2,
  meta 104 24 7 -> 4 (matches the card), and COOL (cooling time) makes no difference at 2 s.
- Pilot (40 random groups, 2 s): costs range 20 .. 4,500. Cost falls with small |G/G'| and with k >= 4. Dihedral-like
  (k = 2) groups are the worst (cost 3,000 to 4,500).

## Results so far
- Screen A chunk 00 running (1.5 s per group, seed 1). Best so far: meta 427 6 13 at N=2562, cost 12.
