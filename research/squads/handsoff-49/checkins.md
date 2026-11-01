# handsoff-49 check-ins

One line per check-in: time (UTC), Opus/Haiku split so far (session_usage budget units, price-weighted), best so far,
what I changed.

- 21:42 setup. Opus/Haiku 0.06/0.00 (setup: read prior work, copied b48 tools, wrote sol2edges.py, verify.sh, cards).
  Best: the table graph 4,970 (rebuilt with haar_tab in 3.5 s, apsp VALID at 9, INVALID at 8). Launched w1-w8 (round 1).
- 22:12 check-in 1. Opus/Haiku 0.114/0.071 (Haiku 38%). No valid claims. Best near misses: w7 bi-coset PSL(2,25), H of
  order 3, n = 5,200, cost 30 (exact minimum for that (G,H) and double-coset shape); w6 surgery on the 4,970 graph,
  n = 4,972, 160 far pairs (every edge of the Haar graph is critical for 179 pairs, 2-switches cost ~350). w1: non-
  metacyclic Haar floors 7-10; w2: 1,779 metacyclic groups listed, screening; w3/w4/w8: evaluators written and checked
  against score48. Changed: w6 handed back twice early (21:55, 22:03); resumed it once with a sharper plan (collect many
  cost-0 bases, pick the one with most slack, 4- and 8-edge surgery). Its background runs continue.
- 22:45 check-in 2. Opus/Haiku 0.148/0.117 (Haiku 44%). No record. Best near misses: w1 Haar of A7 n = 5,040 cost 6;
  w8 2+2 lift over AGL(1,13) x Z_8 n = 4,992 cost 18 (11,232 far pairs); w5 3+3 lift over meta 104 8 31 n = 4,992 cost 19;
  w7 bi-coset PSL(2,25) n = 5,200 cost 30; w6 surgery n = 4,972, 160 far pairs; w4 K44 x Z_622 n = 4,976 cost 156; w3 W(3)
  lift over Z_63 cost 906 (valid 3,200 over Z_40). w2 screened all 1,519 metacyclic groups of order 2,486..2,600 (1.5 s
  each): best 2 (101 25 5, known), 4 (104 24 7, known, and 208 12 3, new), then 6. Changed: w4 proved its own card dead
  (H(3) has girth 12, so two vertices of one fibre of any lift are at distance >= 12 > 9); redirected it to a girth/walk-
  count filter plus lifts of the (4,5) 162 graph and PG(2,3) over non-abelian groups. Added .gitignore for group tables.
- 23:18 check-in 3. Opus/Haiku 0.228/0.155 (Haiku 40.5%). No record. New best near misses: w5 3+3 lift n = 4,992 cost 4
  (same order and cost as the known Haar floor of meta 104 24 7), w2 confirms 5,050 cost 2 and 4,992 cost 4. Finished:
  w7 (74 min; bi-coset exact minima, PSL(2,25) |H| = 3 n = 5,200 cost 30, PSL(3,3) cost 64; perfect groups best),
  w1 (82 min; A_7 Haar exhaustive: minimum 6, ruled out; low cost tracks small centre and abelianization), w3 (85 min;
  W(3) lifts: cost grows with group order, 906 at Z_63; valid only up to 3,200). Changed: launched w9 (bi-coset of M_11,
  S_7, A_8, PSL(2,q) with larger stabilizers, permutation representations), w10 (Haar of centreless small-abelianization
  groups not yet tried: A_5 x AGL(1,7), S_5 x F_21, Z_17^2 x| Z_9, Z_3^5 x| Z_11, ASL(2,5), ...), w11 (exhaustive
  certification of the best metacyclic groups from w2's screen). Fewer, quieter polls from now on to cut Opus spend.
- 23:55 check-in 4. Opus/Haiku 0.281/0.205 (Haiku 42%). No record. w11 certified exhaustively (aut-reduced, all
  triples) 13 metacyclic groups: minima 2 (101 25 5), 4 (104 24 7, 208 12 3), 6, 8, 9: no cost 0. Round 1 closed (w2,
  w4, w5, w6, w8 finished; LOG.md entry). w10 and w11 sat idle 25-30 min "waiting on background work" with nothing
  running: nudged both. Launched w12 (small bases over simple groups, tabu), w13 (the cost-4 wall at 4,992), w14
  (bi-coset, larger simple groups, |H| 4-24), w15 (order 2,500 = P x| Z_4 fixed-point-free, centreless), w16 (quotients
  of the 4,970 graph: 5+5 over 497, 7+7 over 355, 35+35 over Z_71; calibrate, then re-lift over larger groups).
- 00:25 check-in 5. Opus/Haiku 0.343/0.245 (Haiku 41.6%). No record. All 8 round-2 workers active (files touched within
  minutes). New lines: w12 PGL(2,11) 2+2 lift n = 5,280 cost 76 (50,160 far pairs); w15 Heis(5) x Z_5 x| Z_4 (order
  2,500) cost 10. No change; polling less often to cut Opus spend.
- 01:15 check-in 6. No record. Finished since 00:25: w9 (103 min; bi-coset exact minima: S_7 with an involution n = 5,040
  cost 15, M_11 38, PSL(2,25) 30, A_8 168, PSL(3,4) 354), w13 (86 min; the cost-4 wall is the central involution: Haar
  diameter <= 9 iff (S^-1 S)^4 = G on both sides, and (52,0) is far in every cost <= 6 state; all workarounds worse),
  w12 (104 min; lifts over simple groups: PGL(2,11) 2+2 n = 5,280 cost 64, others 88-416). Launched w17 (mixed-orbit
  graphs: regular on A, stabilizers 2 or 4 on B), w18 (auditor: re-score every scoreboard file), w19 (refinement ladder:
  Haar near misses as k+k lifts over index-k subgroups, tabu in the larger space).
