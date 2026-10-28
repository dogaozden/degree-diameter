# c9: freed lines on the D->H friendly transition with concurrent pairs (Q(4,5), types D,H,H)

Test bed: 3 levels, types (D,H,H). t0 = D->H friendly (identity on lines of Q(4,5)); t1 = H->H non-friendly
(points of level 1 -> lines of level 2, index map); t2 = H->D friendly (identity on points). Base graph (no freed sets)
is valid: n=936, d=7, D=5 (apsp VALID).

## Failure without conditions
R0 = 18-line partial spread S (found by local search, maximal: every other line is concurrent with S) plus one line c=5
concurrent with exactly two freed lines 3 and 68. No hubs, no other freed sets:
badcount: 72 ordered pairs at distance > 5 (diameter 6). apsp: RESULT INVALID.
Mechanism (Theorem E, E2): for x in R0 and a point p on partner m not on x, the only line through p meeting x is m itself,
so the matching route of length 4 from x to p is blocked; the parity of the bipartition forces length 4, so the pair fails.

## Repairs tried (all failed; no valid concurrent configuration found)
- R0 = S + c with R2 = ovoid of Q(4,5) (26 points, friendly H->D, valid by itself): still 72 bad.
- Hubs with only two level slots (B-hub = {alpha_c (lvl0 line), sigma_s (lvl2 point)}, A-hub = {tau_w (lvl0 point of an
  ovoid point w on c), beta_m (lvl1 line m)}): the hub itself is far (distance > 5) from the other levels; 186-270 bad pairs.
  The A-hub design that covers the partner pairs ({tau_{w_c}, beta_3, beta_68}, {tau_{w_3}, tau_{w_68}, beta_c}) gives 304 bad.
- Adding a non-friendly freed point p on t1 with a full 3-slot B-hub {alpha_5, p, sigma_s}: 140-194 bad. A single freed
  non-friendly point alone already gives 102 bad, so the H->H transition needs its own repair.

## Conclusion / condition
Hub repair needs hubs that reach every vertex within 5 steps, i.e. full 3-slot hubs (one slot per level) plus Y edges.
That requires freed non-friendly points on t1, which themselves break about 100 pairs and need repair. The concurrency
repair conditions were not found in this time box. The score is therefore the valid partial-spread baseline.

## Valid graph saved
best.edges = 3-level graph with R0 = 18-line partial spread (spread_ls.npy), no hubs, no other freed sets:
apsp: RESULT VALID d=7 D=5 n=936. Score 18 (maximal partial spread found; SAT for 19 and 21 running, see below).
