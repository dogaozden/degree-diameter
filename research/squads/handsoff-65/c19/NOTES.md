# c19 notes: exhaustive Haar search, orders 401-420 (802-840 vertices)

Method. Haar graph H(G,S), |S| = 6, has 2|G| vertices, so |G| in 401..420. Abelian groups are out by the counting bound
(card and shared/README). For every non-abelian group of these orders (353 groups in total: 402:5, 404:3, 405:11,
406:5, 408:43, 410:5, 412:2, 414:8, 416:228, 417:1, 418:3, 420:39; 401, 403, 407, 409, 411, 413, 415, 419 are cyclic
or abelian only) we run shared/haarex3 (copy in c19/haarex3) over all pair classes (r, r2), using
`drive.sh BUDGET`. Groups are exported by haarex2.g (GAP, Aut generators) into c19/g/ORD_ID.txt. Queue order is
groups with few involutions first (queue.txt). Each run is `timeout 300 nice -n 10 ./haarex3 FILE FROM 1000000`; a
run killed by the timeout is resumed from (last PAIR line + 1). A group is closed when its log has a DONE line.
Logs: c19/logs/ORD_ID.out. Per-group progress: c19/status_log.txt.

Calibration (done 18:20):
- SmallGroup(342,12): haarex3 finds 10 VALID sets (e.g. S = 0 2 4 19 118 207) in 10 s. Exported H(G,S) with
  c19/haar_edges.py: apsp_ref gives VALID, d=6 D=5 n=684. The calibration is positive.
- SmallGroup(360,118) = A6: haarex3 closed, VALID 0 (DONE valid=0 minA=-1, 14 s). Negative calibration holds.

Tool note. The harness backgrounds any Bash call longer than 120 s unless timeout is passed; drive.sh was
backgrounded once, then ran to its own budget (no second copy was started).

Progress 18:46 UTC: 402:2/5 404:1/3 405:11/11 406:1/5 408:14/43 410:1/5 412:1/2 414:1/8 416:5/228 417:1/1 418:0/3 420:11/39 
Per-group times 4-65 s so far (orders 402-420). Groups killed by timeout 300 would be resumed (none so far).

Progress 19:30 UTC: 402:5/5 404:3/3 405:11/11 406:5/5 408:43/43 410:5/5 412:2/2 414:2/8 416:54/228 417:1/1 418:0/3 420:17/39 
Queue reordered by order at 19:17 (remaining groups of 402-412 first), so that whole ranges close early.
Closed ranges: 401-406 (scoreboard line written 19:17), 401-412 (scoreboard line written 19:30).
