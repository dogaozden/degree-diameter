# c5b-cosetscreen (handsoff-108): notes

## FOR c8b-coset (read first): better target than PSL(2,181) h = 5

Family K: G = PSL(2,229), H = D5 (order 10 = h), D = one regular double coset H g H (|D| = 100, so c = 10 left
cosets, degree 10). N = |G|/10 = 600,438 per side, 2N = 1,200,876 (> 1,176,480). mu = 77.0 (vertex Poisson), mu/h = 7.7.
- H: r of order 5 in the NONSPLIT torus of PSL(2,229) (5 | (q+1)/2 = 115; C10 does not exist in PSL(2,229)), and an
  involution s inverting r (in PSL, so square determinant). Generator: `SPLIT=0 ./cscreen 229 1 D 10 10 ...`.
- Family size: 59,985 regular double cosets, one member each, so the whole family is about 6e4 members (not 1e8).
  Anneal is the wrong tool; a full scan (about 6e4 x A-root BFS, c8b's fast BFS would take about 1.7 h) is.
- Measured (A-root + B-root cost C = uncBA + uncAA + uncBB, plain units; 260 random members, seeds 108651, 108665):
  median 32.5 units of h (95% bootstrap CI 29.1-36.1), p10 16.6, min 6.6 (66 vertices); C = 0 in none of them.
  Fraction with C/h <= 10: 1.5 %; <= 15: 7.3 %; <= 20: 17 %. All connected; uncBB = 0 for almost all.
  Pooled over 1,060 members (round 1 + K2 + K3, A-root cost): min 5.5 units (55 vertices), 0.28 % at or below 8
  units. Best member: rep key 134144, full C = 55 plain. Details in the round-2 section below.
- Comparison (same method, same units): PSL(2,181) C5 two regular dc (family A, the target so far): median 41.8
  (CI 38.6-46.9, n=300), p10 23.8, fraction <= 15: 0 of 300. PGL(2,181) D5 nonsquare reflection (family C): median
  44.1 (CI 39.9-48.4, n=300), fraction <= 15: 2 %.
- Why it is better: the orbit-model mean is about half as big (mu/h = 7.7 against 13.6), and the measured
  median is also lower in absolute orbit units (32.5 against 41.8), so the tax factor (median/mu = 4.2 against 3.1)
  is the only place it is worse. The absolute median is what sets P(C = 0). Non-regular double cosets
  (k = |H cap gHg^-1| >= 2) are 3-10x worse at the median in every group tested (families E, L, I, H, J, M, F below).
- uncBB > 0 for only 3.5 % of K members (7 of 200), so the A-root BFS alone is close to the full cost.
- Not a record. No member has C = 0; no solution was written. Next step: scan all 59,985 members (A-root BFS
  first; B-root check only for cost 0). Sampling cannot settle it: a rough tail extrapolation gives 0.06 to 60 zeros.


Worker: c5b-cosetscreen (relaunch of slot c5). Seeds 108651-108699 (one seed per family, see families.txt).
Job (card): screen bipartite coset graphs X(G,H,D) over PSL(2,q) / PGL(2,q) for N = |G|/h in [588,241, 610,000],
sample random members, rank families by the uncovered counts, give c8b targets. c8b-coset builds the fast evaluator
and annealer for PSL(2,181), h = 5; this card does not duplicate that.

## Setup

- `cscreen.c` (built from c8-wild/coset2.c, copied, not edited there). Changes:
  - H cyclic C_h or dihedral D_{h/2} (order h), in a chosen torus class (SPLIT=1 split, 0 nonsplit, -1 first found),
    reflection with square / nonsquare determinant (SDET=1 / 0 / -1). Dihedral check: s r s = r^-1.
  - D = union of double cosets H g_i H with c_i = |H g_i H| / h left cosets each (spec "5,5", "5,1,1,1,1,1", ...);
    sum c_i = d = 10. Regular double cosets have c = h; c = h/k with k = |H ∩ g H g^-1|.
  - Full diameter cost C = uncBA + uncAA + uncBB: A-root BFS (A-B and A-A pairs) plus B-root BFS (B-B pairs).
    coset.c / coset2.c check only the A root (c8b-coset found the same).
  - Per member one line: `cand i reps ... uncBA x uncAA y uncBB z C c conn 0|1 ecc e`.
- `families.py`: enumerates (q, PSL/PGL, h, cyclic/dihedral) with N in the window (prime q < 420).
  Only h <= 10 families have many double cosets. For h >= 15 with degree 10 the only double cosets have
  small c (see type counts below); PSL(2,331) D15 has exactly one member (c = 2 x 5), PGL(2,331) D30 likewise.
- `summarize.py`: ranked table from out/*.out and out/*.err (mu, mu/h, min, p10, median, tax, connectivity).
- `run_families.sh` + `families.txt`: runs the list one process at a time (nice -n 10, timeout 3000 s).

Validation (done before the screen): PSL(2,181), H = C5 (first key of order 5), two regular double cosets,
the first 3 candidates of c8-wild/psl181_h5R2_60.tsv: uncBA = 273, 238, 337 and uncAA = 0, identical to coset2
(FIXREPS mode feeds the same double-coset representatives). CHECK=1 on the first member: 5,929,560 edges, 0
asymmetric. uncBB = 0 for the first three.

Cost: about 1 s CPU per member (two BFS). Under the current machine load (~8 on 4 cores) about 2.2 s wall.

Double-coset type counts (c = left cosets per double coset; from the .err headers):
- PSL(2,181), C5: c5: 118,584 regular, c1: 36 (normalizer cosets). Family "5,5" about 7e9 members.
- PGL(2,181), D5 (order 10): c10: 59,202; c5: 180; c2: 17; c1: 2.
- PGL(2,181), C10: c10: 59,292; c1: 36 (no c5 types).
- PSL(2,193), C6: c6: 99,840; c1: 32 (no c3/c2 types). "6,1,1,1,1" is the only way to get degree 10 from C6.
- PSL(2,193), D3 (S3): c6: 99,793; c3: 94; c2: 15; c1: 2.
- PGL(2,193), D6 (order 12): c6: 248; c3: 4; c2: 15; c1: 2. Small.
- PGL(2,193), C12: c12: 49,920; c1: 32. Degree 10 only from c1 types (pure normalizer): not screened.
- PSL(2,331), D15 (order 30): c30: 20,064; c15: 165; c2: 5; c1: 1 -> the only degree-10 spec is 2x5, one member.
- PGL(2,331), D30 (order 60): c30: 174; c15: 1; c2: 5; c1: 1 -> degenerate (one member).

Excluded from the screen as too small or degenerate: PSL(2,331) D15, PGL(2,331) D30, PGL(2,193) C12 with only
normalizer types. Note: PSL(2,229) C10 does not exist (10 divides neither 114 nor 115); PSL(2,229) D5 is in the
nonsplit torus (SPLIT=0).

## Family screen, round 1 (14 families, K = 40-100 members each, seeds 108651-108664)

Units: C = uncBA + uncAA + uncBB (plain vertices, diameter cost, 0 = diameter 8). "units" = vertices / h
(H-orbits of size h). mu = N exp(-5,380,840/N) plain (vertex Poisson); mu/h = orbit model mean.
tax = median C / mu. Ranking by med/h (absolute median in orbit units, lower is better: P(0) is about exp(-median/h)).
Connected = all 2N vertices reached from the A root.

| family (out/<name>.out) | n | N | h | mu/h | min/h | med/h | tax | conn |
|---|---|---|---|---|---|---|---|---|
| K_psl229_D5_10: PSL(2,229), D5 nonsplit torus, one regular dc | 60 | 600,438 | 10 | 7.70 | 8.7 | 34.0 | 4.41 | 1 |
| A_psl181_C5_55: PSL(2,181), C5, two regular dc (c8b reference) | 100 | 592,956 | 5 | 13.58 | 17.8 | 40.7 | 3.00 | 1 |
| C_pgl181_D5_10_nsq: PGL(2,181), D5 (nonsquare reflection), one regular dc | 100 | 592,956 | 10 | 6.79 | 12.7 | 45.7 | 6.72 | 1 |
| H_psl193_S3_631: PSL(2,193), S3, dc c=6,3,1 | 60 | 599,072 | 6 | 12.55 | 16.8 | 108 | 8.64 | 1 |
| G_psl193_C6_6_1x4: PSL(2,193), C6, c=6,1,1,1,1 | 60 | 599,072 | 6 | 12.55 | 123 | 333 | 26.5 | 1 |
| L_psl229_D5_55: PSL(2,229), D5, c=5,5 (k=2) | 60 | 600,438 | 10 | 7.70 | 29.7 | 224 | 29.0 | 1 |
| M_pgl229_D10_10_nsq: PGL(2,229), D10 (h=20), one c=10 dc (k=2) | 40 | 600,438 | 20 | 3.85 | 35.2 | 123 | 31.9 | 1 |
| I_psl193_S3_622: PSL(2,193), S3, c=6,2,2 | 60 | 599,072 | 6 | 12.55 | 146 | 386 | 30.8 | 1 |
| E_pgl181_D5_55_nsq: PGL(2,181), D5, c=5,5 (k=2) | 60 | 592,956 | 10 | 6.79 | 50.5 | 246 | 36.2 | 1 |
| J_pgl193_D6_622_nsq: PGL(2,193), D6 (h=12), c=6,2,2 | 40 | 599,072 | 12 | 6.27 | 160 | 354 | 56.4 | 1 |
| B_psl181_C5_5_1x5: PSL(2,181), C5, c=5,1,1,1,1,1 | 100 | 592,956 | 5 | 13.58 | 632 | 1,765 | 130 | 1 |
| F_pgl181_D5_5221_nsq: PGL(2,181), D5, c=5,2,2,1 | 60 | 592,956 | 10 | 6.79 | 696 | 4,767 | 702 | 1 |
| D_pgl181_D5_10_sq: PGL(2,181), D5 (square reflection), one regular dc | 60 | 592,956 | 10 | 6.79 | - | - | - | 0 (disconnected) |
| N_pgl181_C10_10: PGL(2,181), C10, one regular dc | 10 | 592,956 | 10 | 6.79 | - | - | - | 0 (disconnected) |

Family sizes (number of members, from the type counts): A ~ 118,584 choose 2 = 7e9; B ~ 118,584 x C(36,5) = 4e10;
C 59,202 (a few more with the reflection class); K 59,985 (c10 types); E C(180,2) = 16,110; F 180 x C(17,2) x 2 = 48,960;
G 99,840 x C(32,4) = 3.6e9; H 99,793 x 94 x 2 = 1.9e7; I 99,793 x C(15,2) = 1.0e7; L C(113,2) = 6,328 (c=5 types);
M 135 members of c=10 (k=2) type x 1; J 248 x 4 x 2 = small.

Reading (round 1):
1. Only families with ONE REGULAR double coset per degree block, i.e. |H g H| = h^2 (c = h = 10 for h = 10,
   or two of them for h = 5), have medians below 50 units. Every family with non-regular double cosets
   (k = |H ∩ gHg^-1| >= 2) is 3-10x worse at the median (E, L, I, H, J, M, F, B, G).
2. Square reflection D5 in PGL(2,181): disconnected (H inside the squares: walks keep the determinant class).
   C10 in PGL(2,181): disconnected for the same reason. Degree 10 with h = 10 needs a nonsquare-det element.
3. Best by median in units: K (PSL(2,229) D5, med/h 34.0, n=60), then A (PSL(2,181) C5, 40.7, n=100), then
   C (PGL(2,181) D5, 45.7, n=100). The tax ordering differs (A 3.0 < K 4.4 < C 6.7) because mu/h is half for
   K and C; the absolute median decides P(0). K vs A is within the sampling error at n = 60-100 (see round 2).

## Round 2 (confirmation, fresh seeds 108665-108668, K = 200 / 800)

Runs: K2 (PSL(2,229) D5, seed 108665, 200, full C), C2 (PGL(2,181) D5 nsq, seed 108666, 200, full C),
A2 (PSL(2,181) C5 two regular dc, seed 108667, 200, full C), K3 (PSL(2,229) D5, seed 108668, 800, A-root cost only:
AONLY=1, cscreen2; B-root BFS only for A-root cost 0, which never happened).
Pooled A-root cost uncBA + uncAA (units of h), bootstrap CI for the median by resampling:

| family | n | min | p5 | p10 | median (95% CI) | frac <= 8 | <= 10 | <= 15 | <= 20 |
|---|---|---|---|---|---|---|---|---|---|
| K PSL(2,229) D5, one regular dc | 1,060 | 5.5 | 13.7 | 16.7 | 34.0 (29.1-36.1 for 260 full) | 0.0028 | 0.0151 | 0.0698 | 0.189 |
| A PSL(2,181) C5, two regular dc | 300 | 16.0 | 22.4 | 23.8 | 41.7 (38.6-46.9) | 0 | 0 | 0 | 0.020 |
| C PGL(2,181) D5 nonsquare, one regular dc | 300 | 12.7 | 18.6 | 22.7 | 44.1 (39.9-48.4) | 0 | 0 | 0.020 | 0.063 |

Round 2 verdicts:
- K beats A on the median (about 34 against 42 units, CIs do not overlap) and on the lower tail (K: 0.28 % of
  members at or below 8 units, A: none in 300).
- K is the best family found. Best member: rep key 134144 (cand 124 of the K3 run, seed 108668), full C = 55 plain
  (uncBA 55, uncAA 0, uncBB 0), reproduced with `FIXREPS=best_K_rep.txt SPLIT=0 ./cscreen2 229 1 D 10 10 1 1`.
  Next best (A-root cost, plain): 66, 77, 82, 87, 87 (rep keys 483603, 170791, 170816, 809741, 182225).
- Tail: the log-linear slope of the K tail is about 0.25 per unit between 10 and 20 units, but about 0.8 per unit
  between 8 and 10 (0.28 % at 8, 1.5 % at 10), so the tail gets steeper toward 0. A rough extrapolation puts
  P(C = 0) per member between 1e-6 and 1e-3, i.e. an expected 0.06 to 60 zeros in the 59,985 members of family K.
  This is a guess from 1,060 samples; a full scan is the only real test.

## Summary of families sampled (whole run)

Families tested: 14 in round 1 (table above), plus K2, C2, A2, K3. Two families are disconnected (square reflection
D5 and C10 in PGL(2,181), both with H inside the squares). Largest sample sizes: K 1,060; A 300; C 300.

## Next steps (for c8b and the coordinator)

1. Full scan of family K: all 59,985 regular double cosets of PSL(2,229) (one member each), A-root BFS first and
   the B-root check only for A-root cost 0. With a 0.1 s BFS (c8b's fast code) that is about 1.7 h on one core.
   This is the only way to settle whether a zero exists in the family; sampling cannot.
2. Speed: cscreen2 (A-root only, AONLY=1) takes about 2.5 s per member on the loaded machine; a faster coset
   labelling for PSL(2,229) (c8b's torus trick does not apply to the nonsplit torus) is needed for the full scan.
3. Do not spend more on the h = 6 families (PSL(2,193) C6, S3): medians 108-386 units. Do not spend more on
   families with non-regular double cosets (k >= 2): 3-10x worse everywhere they were tested.
4. Open question: why regular double cosets are better. Non-regular double cosets make words collide
   (H ∩ gHg^-1 ≠ 1 gives short relations); not checked by counting short cycles.

