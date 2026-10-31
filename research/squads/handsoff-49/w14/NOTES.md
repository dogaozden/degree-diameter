# w14 NOTES: bi-coset graphs of larger simple groups with bigger stabilizers (card w14, round 2)

Start: 2026-10-31 23:34 UTC. Deadline: about 01:35 UTC (2 hours). Last update: 23:45 UTC.

## Setup
- grp14.py: copy of w9's grp9.py (H-variant bi-coset graphs, both sides = left cosets of H), extended with groups
  PSL34 (PSL(3,4) on 21 points), PSU34 (PSU(3,4) on 65 isotropic points), PSp43 (= PSU(4,2) on 40 points),
  M12 (12 points), PSLs2_2^4 (= PGammaL(2,16), 16320), PSL2_7^2 (PSL(2,49), 58800). gens14.py makes the generators.
  All group orders checked by closure: 20160, 62400, 25920, 95040, 16320, 58800.
- bi9 (copied from w9, compiled here): exhaustive search over unions of right-H orbits on cosets of total size 4.
  Cost = far vertices from both roots (0 = diameter <= 9).
- Usage: `python3 grp14.py GROUP list [trials]` (classes by order), `python3 grp14.py GROUP h [trials] [exh|rnd:COUNT]`.

## Card facts (my checks)
- PSL(3,4) with |H| = 7 is impossible for degree 4 with H = K: double cosets have size 1 or 7 in H-units, and
  N(H)/H has order 3 (only 3 single-coset double cosets). So use |H| = 8 (n = 5040) only.
- PSL(2,49): order-20 subgroups should not exist (to be confirmed by `list`).
