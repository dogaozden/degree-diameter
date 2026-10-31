# c7 notes (card c7: unstructured local search with a strong engine)

Start: 2026-10-31T15:44:41Z (date -u). Stop about 17:44Z.

## Plan
1. ls7.c: fast cost (same-side ball of radius 6 via 2-step H-graph bitsets, 2 words per row, n <= 256),
   simulated annealing over 2-switches, plus focused proposals (edges near a bad vertex x and near a random
   unreached partner y). Cost = ordered same-side pairs at distance > 6 (0 iff diameter <= 7).
2. Calibrate at n = 150, 160, 168. Then n = 170, 172, 176 from random and from C168.1 + 2 vertices.
3. Tabu variant if SA stalls.

## Engine (15:50-16:05)
- ls7.c: cost = ordered same-side pairs at distance > 6 (= sum over vertices of m - |same-side ball of radius 6|).
  Ball computed on the 2-step graph H per side: B1 = {x} + H(x) (9 entries incl. walks x-b-z), B2 = OR of B1 over H(x),
  B3 = OR of B2 over H(x). Two 64-bit words per row (m <= 128). About 1.5-3 us per full evaluation at n = 150-170.
  Checked against an independent python BFS (out/check_cost.py): n = 150 cost 82 = 82.
- Cost identity: unreached(v) = coll(v) - (127 - m), where coll(v) = number of NB walk collisions; so cost = total
  collisions up to a constant (no smoother surrogate gained from this).
- Move types: random 2-switch (focus_k 0), focused proposal near bad vertex x and an unreached partner y (focus_k 1,
  pf), local 2-switch with u2 a 2-step neighbour of u1 (focus_k 2).

## Calibration (SA, 25-30 s runs unless noted; best = cost, not far)
- n=150, random 2-switch, T 20->1: cost 70; T 5->0.5: 56; T 2->0.3: 82 (acceptance ~0: deltas are ~10-50).
- n=150, focused (focus_k 1) pf 0.5: 76; pf 0.7: 70; pf 0.95: 82 (no gain).
- n=150, LOCAL 2-switch (focus_k 2): T 5->1.5: 44; T 8->1.5: 48; T 4->2: 46; T 12->3: 72.
- n=120: FOUND (cost 0) in 23 s. n=130: best 6 in 30 s. n=140: best 16 in 30 s.
- Insertion start (C168.1 + one pair, n=170, card c1 style): start cost 262 (far 132); random-move SA at T 3->0.3 and
  1->0.2 for 60 s stalls at 96 (far 48 after score37 on the best file, diam 8).
- Tabu (tabu7.c: best of K sampled local moves per step, tenure 15-20): n=150 best 234 (K=50), 132 (K=200) in 30 s.
  Worse than SA: the forced best-of-K move drifts upward. Not pursued unless a full-neighbourhood version is added.
- Machine load is high (load average about 7 on 4 cores, other workers running), so wall times are about 1.5x the nominal.
- n=140, SA local (T 5->1.5, 60 s cycles restarting from best): reached 14 at 56 s, 12 at 177 s; the T=5 restarts drift
  to cost ~200 before cooling, so the cycle start temperature is too hot (wasted time). Run ends at 500 s.
- Insertion start at n=170 with local moves: not yet run (queued after PT test).
- pt7.c written (parallel tempering, R replicas, Tlo..Thi, exchange every sweep); testing next.

## Parallel tempering (pt7.c, R replicas, geometric T ladder, exchange after every sweep of 200 proposals)
- n=140 random start, R=6, T 1.5..6, 300 s: cost 10 (score37 far 5). Compare SA local 12 at 240 s.
- n=150 random start, R=6, T 1.5..3, 400 s: cost 38, score37 far 19.
- n=160 random start, R=6, T 1.5..3, 400 s: cost 106, score37 far 53.
- n=170 from C168.1 + one pair (out/i1.edges, cost 262): cost 92, far 46 (out/pt170.edges). Logged (beats my 48).
- n=170 continued from that cost-92 state at T 1.5..3 for 400 s: no move below 92 (out/pt170b.log). Stuck.
- n=170 from out/i2.edges (another insertion of C168.1 + pair, start cost 392): cost 92 again, far 46.
  Two different insertion starts reach the same cost 92 (far 46) = a strong attractor near C168.1 + 2 vertices.
- Observation: the random-start curve (n=140: 10, n=150: 38, n=160: 106) rises fast. Local search from scratch is
  far from zero already at 150; n=170 is not reachable by this engine from random starts.
- Hot replica note: with Thi = 6 the top pair swap acceptance fell to 0.05 (cost ~550 at the top), so Thi = 3 is used.

## Things that did not help
- Focused proposals (x bad, y unreached partner, focus_k 1): worse than random (76 vs 56 at n=150, 25 s).
- Tabu (best of K sampled local moves): much worse (132-234 at n=150). The forced move drifts uphill.
- SA with T0 = 5 and 60 s cycles restarting from best: wasteful, the restart drifts to cost ~200 before cooling.

## Status at 16:40Z
- Best logged at n=170 by c7: far 46 (out/pt170.edges), ties c1 and c8. No record candidate (far > 0).
- Calibration rows logged: n=140 (far 5/6), n=150 (far 19), n=160 (far 53).
