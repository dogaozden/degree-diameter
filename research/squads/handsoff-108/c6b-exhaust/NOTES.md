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

## Status (updated during the run)

- scanA (A-root part of every class): running K, then C (run_all.sh, nohup, resumable: rerun skips done classes).
  Output: out/K_scanA.tsv, out/C_scanA.tsv (lines: A id orbit sym uBA uAA z00 z01 z10 z11).
