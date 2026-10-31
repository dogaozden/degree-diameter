# c27 status: exhaustive Haar sweep of orders 416, 418, 420 (832-840 vertices). ALL THREE ORDERS CLOSED.

Method: as c19 (shared/haarex3 over all pair classes, one heavy process at a time, timeout 300 nice 10). Driver:
c27/drive.sh BUDGET (copy of c19/drive.sh; each run timeout capped so one call stays under about 290 s). Logs:
c27/logs/ORD_ID.out (c19's logs copied in at start, resumed from there). Closed = DONE line with valid=0 minA=-1.
Starting point (c19, 20:10 UTC): 416 160/228, 418 0/3, 420 17/39.

Per order (non-abelian groups, from c27/queue.txt):
- order 416: 228/228 closed (c19: 160, c27: 68). VALID 0, ASIDE 0. CLOSED.
- order 418: 3/3 closed (c27). VALID 0, ASIDE 0. CLOSED.
- order 420: 39/39 closed (c19: 17, c27: 22). VALID 0, ASIDE 0. CLOSED.

Result: no VALID set (no Haar graph of order 832, 836 or 840 with degree 6 and diameter 5). No record from this sweep.
Calibration (from c19): SmallGroup(342,12) gives VALID sets, so the search finds positives; A6 (360,118) closed with 0.

Progress log (UTC):
- 20:15 416: 13 closed. 20:19 15 more. 20:23 19 more. 20:27 17 more. 20:31 4 more (416 done), 418 done, 420 5 closed.
- 20:35 420: 5 more. 20:39 7 more. 20:41 5 more: 420 done (39/39).

No processes left (checked 20:42).
