# w21 NOTES (handsoff-49): exhaustive minima for the best non-metacyclic groups

Start: 2026-11-01 01:25 UTC. Stop: 02:55 UTC. Last update: 02:51 UTC.

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

## Final status (02:42 UTC)
- S5 x F21: exact minimum **8** (all 34 class reps, no zero). 
- PSL(2,8) x Z5: exact minimum **8** (all 44 class reps, no zero, 20 sets at cost 8). Table: PSL28xZ5.bin (mk_psl28z5.py).
- A5 x S3 x Z7: 53 of 104 class reps (0..52) done, no cost below 9 there; the annealing 8 is in a later rep. Not finished.
- u4m_7 (order 2500, centre 10): 6 of 123 reps, no cost below 4 there. Not finished: about 45 s per class, so
  the full scan needs roughly 90 minutes.
- Why it is slow: central elements act trivially, so the centraliser reduction only divides by |C/Z(G)|. Groups with
  a big centre cost about |Z(G)| times more.
- Next idea: reduce the r-classes with the full Aut(G) (not only inner), and use right/left translation of S to
  normalise e (factor 4). Both are needed to finish u4m_7 and A5 x S3 x Z7 inside one squad session.
- A5 x S3 x Z7 (final, 02:52): reps 0..55 done; cost 8 first appears at rep 55 (elem 105, S = {0,105,176,689}); no cost
  below 8 in reps 0..55. Reps 56..103 not run. Log: a5_*.err / a5_*.out.
