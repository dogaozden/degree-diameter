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
