# w8 NOTES (wildcard)

Start: 2026-10-31 21:41 UTC. Stop (2 hours): about 23:41 UTC.

## Tools (all in w8/)
- wl.c / wl: first version, groups <= 64. wl2.c / wl2: general version (groups <= 4096, base <= 256 vertices,
  parallel base edges allowed with a duplicate-voltage penalty). Usage:
  `wl2 BASE GROUP.bin D seconds seed OUT [T0 T1]`, BASE = "b" then edge lines "u v".
  Cost = (root, lift vertex) pairs at distance > D, plus 1000 per duplicate parallel voltage. Lift far pairs = cost*K/2.
- Evaluator check: far pairs from score48 equal cost*K/2 (checked on the (4,5) base, 57,257 = 3694*31/2).
- Calibration: the dipole base (2 vertices, 4 parallel edges) over meta 71 35 49 with S = {0, 6+71*18, 30+71*19,
  30+71*22} gives VALID 4,970 (score48). NOTE haar_tab element ids are a*k+j; groups.py ids are a+m*j.
  Random SA (60 s) on the dipole does not find cost 0 (stays at cost 2); the search space is too random for SA there.

## Findings
- Lifts of the (4,5) record graph (162 vertices, vertex-transitive, bipartite) over groups of order 31..40:
  cyclic groups stall at cost ~2,150 (about 33k far pairs) after 2 min; non-abelian screen (35 s each) stalls near
  cost 3,100-3,500 (about 50k far pairs). Reason: the number of constraints scales with b^2 k, so a 162-vertex base
  has far too many failing (pair, element) combinations for SA. Dropped.
- Next family: 2+2 bases (b = 4) over groups of order 1,248..1,320 (n = 4k >= 4,972), since n = b k needs k >= 1,243.
  Bases: base4p1.txt (multiplicities [[1,3],[3,1]]), base4p2.txt (all multiplicities 2). Groups built in groups2/.

## Status
- 21:53 UTC: screening 2+2 bases over 5 groups of order 1248..1320 (screen2.txt), 40 s each.
