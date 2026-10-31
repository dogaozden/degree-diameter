# c5b-cosetscreen (handsoff-108): notes

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

## Family screen (in progress)

Table: see below (filled in from out/*.out with summarize.py). mu = N exp(-5,380,840/N) (vertex Poisson, plain),
mu/h = orbit-model mean, tax = median C / mu.
