# Round 5 cards (raise-small-d, 2026-11-02; final round)

Common: read research/squads/raise-small/HEADER.md first. Values to beat now: (3,13) 4,324 · (3,14) 7,040 ·
(4,12) 74,118 · (4,13) 193,058 · (4,14) 498,798.

## What rounds 1-4 found

- Cubic: 2+2 joint lifts (bin/salift_s p = 2) over metacyclic groups hold (3,12) 2,436, (3,13) 4,324 and now (3,14)
  7,040 (Z88 x|_7 Z20, N = 1,760: two of two seeds solved, round 4 f03). Values come from fresh short screens of many
  groups; most groups have a seed-independent floor (cost 2, 4, 6, ...); a cost-2 floor is one missed orbit of pairs at
  distance D + 1, at ordinary elements (not central, not involutions). Chains rarely help.
- Δ = 4: Haar graphs of Frobenius groups Z_p x| Z_k with random S (bin/hmeta) raised (4,12) 74,118 (Z1123 x|_60 Z33),
  (4,13) 193,058 (Z1163 x|_102 Z83: seeds 1-5 stopped at cost 2, seed 6 solved in 22 s) and (4,14) 498,798
  (Z3079 x|_568 Z81). Hmeta costs are also mostly seed-independent per group, but not always (the (4,13) case).
- Swept already: D = 13 2+2 all groups with d >= 8 at N = 1,082-1,120 (best: floors 2 at Z136 x|_53 Z8 and Z55 x|_2 Z20),
  odd groups 1,082-1,500, N = 1,121-1,250 (round 4 f02), >= 1,301 (cost 80+); D = 14 2+2 d >= 8-10 at 1,753-1,850
  (rounds 3-4); the director now sweeps D = 14 2+2 groups with d >= 6 at N = 1,761-1,850 not yet run, ascending.

## Cards

- **g01 (3,13) 2+2, the d = 6, 7 groups at N = 1,082-1,120** (`glist.py 1082 1120 6 6`, keep d < 8) and products
  (Z_m x|_r Z_k) x Z_c with c = 2, 3 at N = 1,082-1,120 (gtab.py 4th argument; sol2edges.py takes c too). 1 seed x 12
  CPU-s each, then 3 more seeds on the 4 lowest.
- **g04 (3,14) 2+2, N = 1,851-1,900**, every group with d >= 6, 1 seed x 12 CPU-s, then 3 seeds on the 4 lowest.
- **g05 (3,14) 2+2, N = 1,901-1,960**, same plan.
- **g06 (4,14) hmeta fresh seeds** over the Frobenius groups of order 249,400-253,000 in
  research/frontier/raise_small/runs/frob414.txt ("N m k r k 1"), 2 seeds x 70 s each, smallest N first.
- **g07 (4,13) hmeta fresh seeds** over the odd Frobenius groups of order 96,530-98,500 in
  research/frontier/raise_small/runs/frob413.txt, 2 seeds x 60 s each.
- **g08 (4,12) hmeta fresh seeds** over the Frobenius groups of order 37,060-37,700 in
  research/frontier/raise_small/runs/frob412.txt, 3 seeds x 40 s each.
