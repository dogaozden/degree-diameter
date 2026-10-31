# w2 NOTES: metacyclic Haar sweep, orders 2,486..2,600

Start: 2026-10-31 21:41 UTC. Planned end: 23:41 UTC. Status at 23:30: sweep finished, no record.

## Result
- No cost-0 Haar graph (no n > 4,970 with diameter 9) in the whole sweep. Best cost 2 at N = 2,525 (n = 5,050),
  Z_101 x|_5 Z_25: this is the floor the card says is proven minimum by exhaustive search, so it is not new.
- Next best floors: cost 4 at N = 2,496 (n = 4,992) for Z_104 x|_7 Z_24 (Z_208 x|_3 Z_12 also gives 4),
  cost 6 at N = 2,520: Z_105 x|_17 Z_24, Z_35 x|_4 Z_72, Z_420 x|_109 Z_6 (split); Z_140 x|_9 Z_18 and Z_210 x|_17 Z_12 (non-split, s = 35 or 105).
- The scoreboard has two w2 lines (cost 4 at n=4992, cost 2 at n=5050), both VALID=no.
- No records/ file (no cost-0 run). The cost-2 result has no solution file: haar_tab writes a solution only at cost 0.
  Reproduce the cost-2 floor with: `haar_tab 4 9 8 2 8 OUT meta 101 25 5 1` (seeds 2 and 3 at 8 s both gave 2 in
  deep.tsv).

## Coverage (all screened with `haar_tab 4 9 1.5 1 8`, one seed, then deepened)
- Split metacyclic, k >= 3, |G/G'| <= 200: 937 groups (`screen_A.txt`, `screenA.tsv`).
- Split metacyclic, k >= 3, |G/G'| > 200: 582 groups (`screenB.tsv`); best 356.
- Split, k = 2 (dihedral-like): 260 groups (`screenK2.tsv`); best 1,506. Total 1,779 = `enum_groups.py 2486 2600`.
- Non-split metacyclic (b^k = a^s, s(r-1) = 0 mod m, s != 0), one s per (m,k,r) with s = m/gcd(r-1,m), k >= 3,
  k*gcd(r-1,m) <= 200: 686 groups (`ns_A.txt`, `nsA.tsv`), built as `tab` tables (`nonsplit.py`); best 4.
  Not done: other s values per (m,k,r), and non-split groups with k*gcd > 200.
- All tables merged: `sweep_table.tsv` (1,779 split rows; non-split rows are in `nsA.tsv`).

## Deepening
- deep.tsv: top 12 (8 s, seeds 2 and 3) and top 4 more (60 s, seeds 5 and 6). All floors held: no run went below the
  1.5 s value. Longer runs did not move any floor.

## Calibration and tools
- Known good group 71 35 49 reaches cost 0 in 3.7 s; 2 s runs reproduce 104 24 7 at cost 4.
- Pilot (40 random groups, 2 s) showed the cost falls with small |G/G'| and with k >= 4.
- Workflow: `enum_groups.py`, `screen.sh` (split), `ns_screen.sh` + `nonsplit.py` (non-split, tables in /dev/shm),
  `deepen.sh`, `topN.sh`, `feat.py`. A `pgrep -f` wait loop matches itself and never exits; use the PID instead.

## What I would try next
- Non-split metacyclic groups with other s values per (m,k,r) and k*gcd > 200 (not screened), then a 60-s run on
  any with cost <= 2 at N >= 2,486.
- Exhaustive S-search (exh_meta style) only where gcd(r-1,m) = 1, to test whether the 2,496 and 2,520 floors (cost 4 and
  6) are real. The exhaustive run for one group is about 10^8 evaluations, so budget ~1 hour per group.
