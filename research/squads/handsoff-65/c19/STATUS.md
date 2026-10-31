# c19 status: exhaustive Haar search on orders 401-420 (802-840 vertices), final at 20:10 UTC

Result: no VALID set and no side-A cover (ASIDE 0) found in any closed group. No record.

Closed (all non-abelian groups of the order, every pair class searched by haarex3, DONE line, valid=0):
- orders 401-415 as a range: 402 (5/5), 404 (3/3), 405 (11/11), 406 (5/5), 408 (43/43), 410 (5/5), 412 (2/2),
  414 (8/8). Orders 401, 403, 407, 409, 411, 413, 415 have only abelian groups (out by the counting bound).
- order 417: 1/1 (its only non-abelian group).
Open at the stop: order 416 (160 of 228 closed, 68 left), order 418 (0 of 3), order 420 (17 of 39). Order 419 has
only abelian groups.

Calibration: SmallGroup(342,12) gives 10 VALID sets (S = 0 2 4 19 118 207 verified: apsp_ref VALID d=6 D=5 n=684).
A6 = SmallGroup(360,118) closed with valid=0.

Summary per order (closed/total non-abelian): 402:5/5 404:3/3 405:11/11 406:5/5 408:43/43 410:5/5 412:2/2 414:8/8 416:160/228 417:1/1 418:0/3 420:17/39 
Logs: logs/ORD_ID.out (haarex3 output), status_log.txt (one line per group run). Scoreboard: lines for 401-406 and
401-415 closed were appended (401-415 line says 416-420 in progress). No line for 416/420: not closed.
Resume: ./drive.sh BUDGET (resumes a killed group from its last PAIR line; closed groups are skipped).
