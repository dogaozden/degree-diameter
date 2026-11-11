# c6b-exhaust (handsoff-108): notes

Worker: c6b-exhaust (relaunch of slot c6, card at the end of ../cards.md). Job: scan EVERY regular double coset of two
families with h = 10 and one double coset (degree 10):
- C: G = PGL(2,181), H = D5 = <diag(1,42), [[0,1],[2,0]]> (nonsquare reflection, same H as c5b's C family), N = 592,956.
- K: G = PSL(2,229), H = D5 = <[[1,1],[1,27]], [[1,0],[26,228]]> (order-5 element in the non-split torus, same H as
  c5b's K family), N = 600,438.
Cost C = uBA + uAA + uBB in plain vertices (0 = diameter 8), as fastc.c / c5b cscreen.

## Code (exh.c, built to exh; run_all.sh; validate.py; summ.py)

- Generic group labels, no torus formulas: every element of G is stored under a key (normalised matrix: det scaled to
  1 or to the non-square class, sign fixed). T[key] = left coset label (|G| uint32 entries, 24 MB; 2 MB aligned, madvise).
  Coset H x = {h x}. N = |G|/10 labels (checked).
- Double cosets H z H = orbits of H acting on the right on H\G with trivial stabiliser (10 distinct cosets).
  Counts: C 59,202 regular (c5b: c10 59,202), K 59,985 regular (c5b: c10 59,985). Both match.
- Neighbours: A-vertex Hx has B-neighbours H z^-1 h x (h in H); B-vertex Hy has A-neighbours H z h y.
- BFS: as fastc (bitsets, direction-optimising), batched: keys of the 10 neighbours are computed and prefetched;
  bottom-up uses neighbours 0-2 first, then 3-9 only for the vertices not yet found.

## Symmetry (classes)

- X(G,H,D^-1) = X(G,H,D) with the sides swapped, so C(D^-1) = C(D). For self-inverse D the side swap is an
  automorphism, so uBB(D) = uAA(D) (C = uBA + 2 uAA, one BFS).
- X(G,H,nDn^-1) = X(G,H,D) for n in N_PGL(H) (map Hx -> Hnx). N_PGL(H) has order 20 in both families (H itself is 10
  of it; H acts trivially on double cosets).
- Classes = orbits of <inversion, conjugation by N_PGL(H)>: C 16,407 classes (orbit sizes 1, 2, 4: 90, 3,078, 13,239),
  K 16,293 classes (orbit sizes 1, 2, 4: 57, 2,508, 13,728). Each class is scanned once via its smallest id.
  Self-inverse double cosets: C 3,168 (c. 5 %), K 2,565.

## Validation

- validate.py: the first 10 members of c5b's C and K output (same H, same double-coset representative keys) give
  uBA, uAA, uBB identical to c5b's cscreen on all 20 (including the nonzero ones: C cand 3 uBB 1, cand 8 uBB 3;
  K cand 6 uBA 141864 uAA 232 uBB 240).
- symtest: C(D) = C(D^-1) = C(nDn^-1) on 12 random classes; uBB = uAA on 12 self-inverse classes. No mismatch.

## Speed

- About 0.13 s CPU per BFS (about 4.5 M neighbour evaluations; L3-latency bound; the machine is oversubscribed,
  load 7-8 on 4 cores, so wall time is about 0.2 s per class). Full A-root pass of one family: about 55 min.
- Two BFS per class are needed for the full cost (A root and B root), except self-inverse classes.

## Scope change (coordinator, 00:30 UTC)

- Family C is NOT scanned here (worker c5c-scanC runs C with a copy of exh.c). The wrapper run_all.sh was stopped
  before its C step (the K process itself ran to the end). C has no results in this folder.
- B-root pass only for classes with uBA + uAA <= 50, best first (out/K_le50_sorted.tsv -> out/K_scanB.tsv).

## Results: family K (PSL(2,229), D5 in the non-split torus, 59,985 regular double cosets)

- A-root pass: all 16,293 classes (out/K_scanA.tsv, orbit sizes sum to 59,985). Took about 56 min.
- B-root pass: the 10 classes with uBA + uAA <= 50 (40 members). All are non-self-inverse, so their full cost needs the
  B-root BFS; the other classes with P <= 50 do not exist.
- Self-inverse classes (1,311 classes = 2,565 members): full cost exact from the A-root pass (uBB = uAA), C = uBA + 2 uAA.
- Lower bound for every other class: C >= P = uBA + uAA (uBB not computed; it was 0 in 56 of 60 random c5b members).

Exact top 10 (C = uBA + uAA + uBB, plain vertices; each class = 4 members; z = normalised representative):

| C | class id | uBA | uAA | uBB | z |
|---|---|---|---|---|---|
| 4 | 4233 | 4 | 0 | 0 | (1, 20, 220, 50) |
| 33 | 576 | 33 | 0 | 0 | (1, 3, 126, 150) |
| 37 | 20585 | 37 | 0 | 0 | (1, 111, 140, 198) |
| 41 | 7517 | 41 | 0 | 0 | (1, 37, 123, 201) |
| 42 | 3123 | 42 | 0 | 0 | (1, 15, 209, 159) |
| 45 | 27321 | 45 | 0 | 0 | (1, 158, 191, 180) |
| 45 | 29873 | 45 | 0 | 0 | (1, 179, 89, 131) |
| 46 | 2715 | 46 | 0 | 0 | (1, 13, 135, 153) |
| 47 | 4555 | 47 | 0 | 0 | (1, 23, 100, 11) |
| 50 | 2048 | 50 | 0 | 0 | (1, 10, 24, 12) |

- Best member: class 4233, C = 4 (uncovered, not diameter 8). Re-checked with `exh member 1 20 220 50`: uBA 4, uAA 0,
  uBB 0. Independent check by the coordinator is still needed. No cost 0 found; no CLAIM.
- Distribution over all 59,985 members (weighted by orbit size): min 4 (exact); P quantiles (lower bounds of C):
  p0.1 = 54, p1 = 92, p10 = 161, median = 338. Self-inverse members have exact C. The median and p1 of C can be a few
  units higher than P if uBB > 0 (56 of 60 random c5b K members have uBB = 0).
- Summary: `python3 summ.py K`.

## Files

- exh.c / exh (the evaluator), validate.py (20 members of c5b checked identically), summ.py, run_all.sh (wrapper, killed
  before C), out/K_scanA.tsv, out/K_scanB.tsv, out/K_le50_sorted.tsv, out/*.log.
- Validation: 20/20 members identical to c5b's cscreen (uBA, uAA, uBB). symtest: 12 random + 12 self-inverse classes,
  C(D) = C(D^-1) = C(nDn^-1) and uBB = uAA for self-inverse, no mismatch.
- Scoreboard: one line for the K best (C = 4, plain).
