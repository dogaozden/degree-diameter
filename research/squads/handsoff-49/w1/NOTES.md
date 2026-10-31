# w1 NOTES (handsoff-49): Haar graphs of non-metacyclic groups, N = 2,486..2,700 (n = 2N)

Start: 2026-10-31 21:41 UTC. Planned end: 23:41 UTC.

## Facts I established
- Haar H(G,S), S = {e,s1,s2,s3}: A-side needs B4(U)=G with U = S^-1 S, B-side needs B4(V)=G with V = S S^-1
  (B4 = ball of radius 4; cost = uncovered counts, same as haar_tab). Checked numerically (cov.py, dbg.py).
- Walks are NOT free: U.U collapses (|B2(U)| = 121 not 145), so a random S in A7 has cost ~70; the annealer gets ~12.
- Haar graphs of non-meta groups seem to floor at cost 7-10 at N ~ 2520-2640 (short annealing).

## Results so far (haar_tab, 4-8 s, seed 1; cost = both sides)
- psl 7 x Z15 (N 2520): 10 | pgl 5 x Z21: 7 | psl 8 x Z5: 8 | psl 5 x Z42 (A5 x Z42) 28, sl 5 x Z21: 36
- prod psl 5 x (S3) x Z7 (N 2520): 8 | A7 (perm table, N 2520): 12 (8 s)
- sl 11 x Z2 (2640): 14 | psl 9 x Z7 (2520): 13 | psl 11 x Z4: 26
- sl 7 x Z8, psl 7 x Z16, csl 7 x Z16 (2688): 20-24 | tpgl 7 x Z8: 77
- agl1 families: 15 (23x5) to 1346 (7x60). S4 x Z105 406, A4xA4xZ18 160 (big abelianization is bad).
- abelian-by-cyclic non-meta list (abc.py list, 23 groups in 2486..2700), 6 s each:
  abc k15 (11:5:1,2:15:4) N 2640 -> 10 ; abc k9 (2:3:2,73:9:1) N 2628 -> 10 ; k11 (3:11:5) N 2673 -> 22;
  the rest 22..2600 (k=3 groups ~2300: useless).

## Tools I wrote (w1/)
- cov.py: numpy cost of a group table and random-S statistics. exh.c/exh: exhaustive scan over class reps
  (too slow: ~100 us per S; full A7 scan would need ~40 min on one core, not done yet).

## Next
- Deepen the top 4 (abc 2640, abc 2628, psl 8 x Z5, pgl 5 x Z21) with 2 min runs.
- Non-meta families still unscreened: Heisenberg x Z_n (heis 5 x Z20 = 2500, heis 3 x Z_n n=93..100), Z_p^2 x| Z_k
  (semi), Z_11^3 x| Z_24-type. Then deepen whatever is closest.
