# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-31, job selfdual-d5c, round sd5c-r1 (06:42-07:24 UTC), goal (13,5) > 11,700

Context: formula-only self-dual tabu `research/selfdual-d5c/src/fsd` at K = 13. Calibration solved C41 : C110 (order
4,510) and C251 : C20 (5,020); typical groups at the target order 5,851+ stay at 20-30 (C61 : C96, C163 : C36), C61 : C90
(5,490) at 12. The director screened the 5,851-5,950 formula groups (metacyclic, x C_n, affine, PSL) on 2 cores during
the round. Rules `sd5c-r1/COMMON.md`, cards `sd5c-r1/CARDS.md`, scoreboard `sd5c-r1/scoreboard.jsonl`.
Cards: c1 non-split metacyclic (y^k = x^s) · c2 F_p^2 : C_k with a non-scalar matrix action · c3 metacyclic groups
outside the director's list (even m, large unmoved factor) · c4 clause-weighted tabu · c5 annealing / late acceptance ·
c6 Heis(p) x metacyclic · c7 wildcard (it chose moves aimed at a random uncovered element) · c8 wildcard (it chose
direct products of two metacyclic groups).
Best per card (energy |G \ X X| at order >= 5,851 unless stated, 0 = valid; nothing valid): c1 50 (C302 non-split,
6,040; 68 at 5,960; read from its logs after hand-back) · c2 35 (F7^2 : C120, diag(3,5), 5,880) · c3 36 (C247 : C24,
5,928) · c4 10 on C61 : C90 (5,490) against plain 11-13, and 2-6 against plain 2-4 on C251 : C20 (no clear gain) ·
c5 no solution on C251 : C20 in 3 x 120 s (plain tabu did not solve it either under the round's load, so not
conclusive) · c6 42 (Heis(3) x (C73 : C3), 5,913) · c7 104 on C61 : C96 (plain 20: worse) · c8 44 ((C5 : C8) x
(C7 : C21), 5,880; its calibration did not reproduce the plain solve, the factor-automorphism family is too narrow).
Kept / learned: every new family is worse than plain metacyclic C_p : C_k at the same order (20-24); none of the
search variants beats the tabu. Process notes: three cards ran background jobs and handed back early; two created
one-shot scheduled messages into the director's session, which the director deleted; one card's tool list showed
an interrupt_session call (target not identified). Next cards should say "no scheduled tasks, no session tools".
What next (director): no second round; the metacyclic screen of 5,851-5,950 continues on 4 cores, then probes at
(12,5), (14,5), (15,5), (16,5).
Outcome of the job (director, 09:55 UTC): the screen of all 143 metacyclic groups of order 5,851-5,950 (plus the affine
groups, PSL(2,11) x C9 and a sample of direct products) ended at best 20; 600 s deep runs on the four best stayed at
18-24; probes above the (12,5), (14,5), (15,5), (16,5) targets at 57, 104, 70, 440. No record
(research/selfdual-d5c/README.md).
