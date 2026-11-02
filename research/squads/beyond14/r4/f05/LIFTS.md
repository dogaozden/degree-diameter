# f05: why tiny-base lifts behave differently across p and Delta (start-state statistics only)

Tool: f05probe.c (this folder). Random cubic/quartic bipartite base (d random perfect matchings, p+p vertices, connected),
random voltages in a metacyclic group Z_m x|_r Z_k (implicit multiplication), D = 14. Per state: cost (pairs (source, vertex)
beyond distance 14, same definition as salift_s), mean ball size B13, E13 = mean over roots of the number of distinct
endpoints of all non-backtracking (NB) walks of length <= 13, root-component size. Checked: cost agrees with an independent
Python BFS (n = 220, D = 6: 446 = 446), and a cost-0 lift (n = 6040, Delta = 3) is VALID in bin/apsp (diameter 14).

Raw data: BK_d3p*.txt, F1_d3p*.txt, F2_d3p*.txt, AB_d3p*.txt (Delta = 3), D4_p1.txt, D4_p2.txt, D4_p2_k31.txt (Delta = 4).
Summary: python3 summ.py FILE... (median/min/quartiles of cost, connected fraction, E13/n).

## Counts that do not depend on the group
- NB walks of length <= 13 from a root: 24,573 (d = 3), 3,188,644 (d = 4), for every p. A cubic lift of n = 6,000 vertices
  therefore has about 4 walks per vertex to spread over; a quartic lift at n = 503K about 6.3.
- Free data per lift: cycle rank of a d-regular base on 2p vertices is dp - 2p + 1 = (d-2)p + 1 after a spanning-tree gauge.
  For d = 3: p + 1 voltages, i.e. (p+1)/(2p) voltages per base vertex: 1.00, 0.75, 0.67, 0.63 for p = 1..4. Group bits at
  n = 6000: 2 log2 N = 23.1 (p = 1), 3 log2 N = 31.6 (p = 2), 4 log2 N = 39.8 (p = 3), 5 log2 N = 47.8 (p = 4). Base choice
  and Aut(G) are not divided out here (not counted).

## Delta = 3, matched n about 6,000, 200 random states per group (median cost, min cost, E13/n median)
Faithful groups (r has order k):
| p | group | n | min | median | connected | E13/n |
|---|---|---|---|---|---|---|
| 1 | Z601 x| Z5 | 6010 | 1266 | 3868 | 0.95 | 0.54 |
| 2 | Z499 x| Z3 | 5988 | 1286 | 9304 | 0.97 | 0.48 |
| 3 | Z331 x| Z3 | 5958 | 232 | 2478 | 1.00 | 0.81 |
| 4 | Z151 x| Z5 | 6040 | 4 | 142 | 1.00 | 0.96 |
| 1 | Z499 x| Z6 | 5988 | 9492 | 11092 | 0.68 | 0.06 |
| 2 | Z373 x| Z4 | 5968 | 978 | 14199 | 0.88 | 0.34 |
| 3 | Z71 x| Z14 | 5964 | 16 | 239 | 0.95 | 0.94 |
| 4 | Z127 x| Z6 | 6096 | 102 | 2879 | 0.95 | 0.82 |
Larger k (the action group Z_k has k >= 11):
| p | group | n | min | median | connected | E13/n |
|---|---|---|---|---|---|---|
| 1 | Z211 x| Z14 | 5908 | 22 | 835 | 0.75 | 0.81 |
| 2 | Z151 x| Z10 (r of order 5, centre Z2) | 6040 | 0 | 196 | 0.82 | 0.94 |
| 3 | Z71 x| Z14 | 5964 | 4 | 74 | 0.93 | 0.97 |
| 4 | Z67 x| Z11 | 5896 | 4 | 64 | 1.00 | 0.97 |
Abelian controls Z_m x Z_k (r = 1), same orders: Z499 x Z6 min 11,344 median 11,344, E13/n 0.05; Z499 x Z3 min 17,464
median 17,620, E13/n 0.22; Z151 x Z5 min 1,802 median 7,840, E13/n 0.71.

## Delta = 4, n about 503K, 50-60 states (one root for E13)
| p | group | n | min | median | E13/n |
|---|---|---|---|---|---|
| 1 | Z5849 x| Z43 (record group order) | 503,014 | 28 | 82 | 0.975 |
| 2 | Z41911 x| Z3 | 502,932 | 461,466 | 747,102 | 0.42 |
| 2 | Z4093 x| Z31 | 507,532 | 42 | 104 | 0.978 |

## What the data say, in plain words
1. At matched vertex count the group changes the start cost far more than p does. Within one p, moving from a group with
   action order k = 3-6 to one with k >= 10 changes the median cost by one to two orders of magnitude (Delta = 4, p = 2:
   747,102 -> 104; Delta = 3, p = 3: 2,478 -> 74). The p-ordering flips between the two group sets at Delta = 3.
   So the "tiny base wins at Delta = 3" pattern cannot be attributed to p with these data.
2. The cause visible in the data is the endpoint count. In groups whose action is by a small multiplier set, NB walks of
   length <= 13 reach only a few percent to half of the vertices (E13/n 0.05-0.5), and abelian groups are worst. Words in a
   nearly commutative group are determined by how often each generator is used, so they collapse to a polynomial number of
   endpoints instead of spreading out. Good groups (k large, or a larger nonabelian action) give E13/n 0.94-0.98.
3. Some random states are disconnected in the small-k families (only 68-75% connected for two of them); their cost is then
   large for reasons unrelated to diameter tuning.
4. At Delta = 4, p = 1 and p = 2 are equally good once the group action is large (medians 82 and 104; E13/n 0.975 and
   0.978). A 2+2 lift is not intrinsically worse at Delta = 4; the earlier bad result (r3/e07) and the 747K median above
   are a group effect.
5. The probe found a random state with cost 0 at n = 6040, Delta = 3 (p = 2, Z151 x| Z10): VALID by bin/apsp. This is
   below the record 7,004 and is not a new record. It shows that at n = 6000 about 1 in 200 random lifts of this group
   already work, so the search difficulty is set by the size and group, not by a missing trick.

## Limits
- Metacyclic groups only (no SL/PSL, which are the record groups). Random states only; no annealing.
- Only the group orders and actions above were tried, one group per (p, family). The p-effects in items 1 and 4 are
  therefore conclusions about these groups; more groups per cell would be needed for a sharper claim.
- In all runs E13 equals the BFS ball of radius 13 to within rounding (B13 and E13 agree).

## Addendum: more faithful groups with k >= 11 (Delta = 3, n about 5,900-6,200, 200 states each)
| p | group | n | min cost | median cost | E13/n median | cost-0 states |
|---|---|---|---|---|---|---|
| 1 | Z109 x| Z27 | 5886 | 0 | 34 | 11 of 200 (not measured) |
| 1 | Z211 x| Z14 | 5908 | 22 | 837 | 0 of 200 (E13/n 0.81) |
| 2 | Z67 x| Z22 | 5896 | 2 | 159 | 0 of 200 (E13/n not measured) |
| 2 | Z97 x| Z16 | 6208 | 16 | 346 | 0 of 200 |
| 2 | Z151 x| Z10 (r order 5) | 6040 | 0 | 196 | 1 of 200 (E13/n 0.94) |
| 3 | Z89 x| Z11 | 5874 | 0 | 46 | 1 of 200 |
| 3 | Z71 x| Z14 | 5964 | 8 | 269 | 0 of 200 |
| 4 | Z67 x| Z11 | 5896 | 2 | 62 | 0 of 200 |
| 4 | Z61 x| Z12 | 5856 | 25 | 507 | 0 of 200 |
Per-file counts: zero_counts.txt. Cost 0 at these n is below the record 7,004, so none of this is a record.
Reading: cost-0 states appear for p = 1, 2, 3 at n about 5,900-6,000 but not for p = 4 in 200 states, and the ordering of
medians across p changes with the group. The data do not support a p-only ranking at matched n.
