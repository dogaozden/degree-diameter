# w21 NOTES (handsoff-49): exhaustive minima for the best non-metacyclic groups

Start: 2026-11-01 01:25 UTC. Stop: 02:55 UTC. Last update: 02:01 UTC.

## Method (exh2.c, in this folder)
- Same cost as w1's exh.c: cost = uncovered(B4(S^-1 S)) + uncovered(B4(S S^-1)), zero iff diameter <= 9.
- S = {e, r, b, c}, r over one representative per non-identity conjugacy class. For fixed r, C = C_G(r).
  Conjugation by h in C fixes e and r, so b runs over C-conjugation orbit reps and c over C_b-orbit reps, where
  C_b = {h in C : h b h^-1 = b}. Every S containing e is conjugate to one of these, so the scan is exhaustive up to
  inner automorphism.
- Check: exh2 reproduces w1/w10 results on S5 x F21 (reps 0,1 best 9; reps 10,11 best 8).
- Limit: central elements act trivially, so the reduction is only by C/Z(G). Work per group is about N^2 / |C/Z|
  evaluations. Groups with a big centre are slow (u4m_7 about 45 s per class, 123 classes; not finishable in time).

## Exact results (exact.tsv)
- S5 x F21 (order 2520, centre 1): **exact minimum 8**, all 34 class reps, 360 s. No zero. Matches the annealing floor.
- PSL(2,8) x Z5 (order 2520, centre 5): running (see exact.tsv for the state).
- u4m_7 (order 2500, centre 10, floor 4 by annealing): partial only; run stopped for time (see exact.tsv).

## Files
- exh2.c / exh2: the exhaustive scan. exact.tsv: group, order, minimum, classes covered, seconds.
- S5xF21.bin (copied from w10/tabs), u4m_7.bin (copy of w15/tabs), PSL28xZ5.bin (mk_psl28z5.py: SL(2,8) x Z5 over GF(8)).
- S5xF21_full.out / .err, u4m_7_full.out / .err, psl_full.out / .err: raw logs.
