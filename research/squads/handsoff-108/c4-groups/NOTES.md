# c4-groups (worker c4, squad handsoff-108): screen of direct-product groups for N in [588241, 600000]

Goal: a Haar graph with Delta 10, D 8 and N = |Q| n >= 588241 (2N > 1,176,480). Card: `../cards.md` (c4-groups).

## Setup (2026-10-31, from 21:45 UTC)
- Candidates: `enumerate_groups.py` (k = 3) -> `candidates.tsv`: 3850 groups Q x Z_n with N in window.
  Families: sl q, pgl q, psl q (odd q), agl1 q, meta p k r (p prime, k | p-1, k >= 3; one group per (p,k)),
  products of two base groups (meta excluded from products), n = 1 or n with all prime factors = 1 mod 3.
  Counts: sl 257, pgl 257, psl 123, agl1 413, prod 736, meta 2064 (n=1 and n>1 mixed).
- Screen: `screen.py` runs `ORBIT="3 3 1" RANDORB=300 ORBW=3 haar_sym2 10 8 1 108501 8 /dev/null <spec>` (one
  process at a time, nice 10, timeout 120 s). Output `screen300.tsv` (N, family, spec, mu, fix, min, p1, p10,
  median, secs, status). `rank.py screen300.tsv 30` ranks by (p1+p10)/2/mu.
- Reference (same screen): psl 23 97 at RANDORB=300 is in the table; card numbers (RANDORB=1000): min 36, p1 52,
  p10 84, median 135. Own RANDORB=1000 run of psl 23 97 (seed 108501): min 38, p1 55, p10 78, median 138.
- Deviation from the card: RANDORB=300 for the screen (1000 for the top ones later), because of the time budget.

## Costs found while screening (why the list is not all done)
- Groups with no cyclic subgroup of order 64-63 (meta groups, and n = 1 products of small groups) take haar_sym2's
  slow path ("wide rows: no cyclic subgroup of order >= 64"): about 0.2 s per sample instead of 0.01 s.
  Meta candidates with n = 1 cost 15-20 s each at 300 samples. The 2064 meta candidates would take many hours.
- Groups with large cyclic factors (n > 500) cost 5-20 s each at 300 samples.
