# Squad round table-audit-r1 (2026-10-25)

Goal: reach (at least) the table order, with a graph that passes apsp.c, in the five small cells whose holder's graph
is lost: (3,8) = 256 and (3,10) = 800 (Delorme–Gómez–Quisquater, never published; (3,10) unbeaten by the repo),
(6,5) = 684, (4,8) = 2,184, (4,9) = 4,970 (Loz; data lost; unbeaten by the repo).
Scorer: `bin/apsp EDGES d D` (copy of research/lifts/coordinator_check/apsp.c) must print `RESULT VALID` with n >= the
table value. Board: scoreboard.jsonl (one line per card). Plain metacyclic Haar graphs via haar_gen3 are run by the
lead separately and are excluded from the cards.
bin/ holds binaries compiled from repo sources (not committed).
