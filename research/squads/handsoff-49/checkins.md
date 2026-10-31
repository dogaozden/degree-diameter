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
