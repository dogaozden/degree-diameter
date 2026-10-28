# r3c4: small-q test of Proposition 7.2 (A-hub condition only), D5_QUADRANGLE.md section 7

Setup. G = Q4(q) = W(q).dual(), 5 levels, types H H D H D, rotational tournament j -> j+1, j+2 (mod 5), r = 2,
level degree q+3, hub degree q+3 (5 level slots + q-r hub-graph edges).
- H->D arcs 0->2, 1->2, 3->4 free the ovoid O (regular spread of W(q), q^2+1 points); identity matchings.
- D->H arcs 2->3, 4->0, 4->1 free the same relaxed set T of lines of G; identity matchings.
- Non-friendly arcs 0->1, 1->3, 3->0 (H->H, on G) and 2->4 (D->D, on W(q)): two-point local duality (localdual.py),
  two freed elements each.
- B-hubs: one A-slot per level, ARBITRARY (no rule).
- A-hubs: for each partnered line l (partner m, ovoid point o_m): one A-hub holds the B-slots (l, 4->0) at level 0,
  (l, 4->1) at level 1, (l, 2->3) at level 3, the B-slot at o_m in level 2 (copy from 0->2) and at o_m in level 4 (from
  3->4). This is Proposition 7.2's rule. Other A-hubs arbitrary.
  (Observation: the two D->H arcs out of level 4 force the same hub, so one A-hub per partnered line suffices. The text
  of Prop. 7.2 mentions one per partnered line and per D-level; ours is a special case that needs fewer hubs.)
- Hub graph Y: degree q-r, annealed by hubopt.search so that same-colour hubs are within distance 4 (hub_bad = 0).

Relaxed sets. relaxed.c (the d5gq annealer, compiled here) on W(5): 4 seeds x 60 s, all reach 23 points with 6 partner
pairs (counting bound 28). T5_s1.txt = the set used (also T5_s2..s4). On W(7): one 120 s run, 41 points, 15 pairs
(counting bound 53); T7_s1.txt. Relaxed-set conditions were checked by build.py (each line meets at most one other
line of T; meeting point not on O).

Results (apsp binary: ./apsp EDGES d D with d = q+1+r, D = 5; prints VALID/INVALID).

| graph | q | pairs | rule | n | D=5 | D=6 |
|---|---|---|---|---|---|---|
| rule_s1.edges | 5 | 6 | A-hub rule holds (check_rule.py: no violations) | 1610 | VALID d=8 | VALID d=8 |
| break4_s1.edges | 5 | 6 | rule broken for line 16: its A-hub's level-4 slot moved from o_m=117 to point 0 (not on m=93) | 1610 | INVALID (diameter 6) | VALID |
| break2_s1.edges | 5 | 6 | rule broken for line 16: its A-hub's level-2 slot moved from 117 to point 0 | 1610 | INVALID (diameter 6) | VALID |
| rule7_s1.edges | 7 | 15 | A-hub rule holds | 4086 | VALID d=10 | VALID d=10 |
| break47_s1.edges | 7 | 15 | rule broken for line 16 (level-4 slot moved to point 0 off partner 243) | 4086 | INVALID (diameter 6) | VALID |
| break27_s1.edges | 7 | 15 | rule broken for line 16 (level-2 slot moved to point 0) | 4086 | INVALID (diameter 6) | VALID |

Degrees: maximum q+3 (= d = q+1+r) in every graph; minimum 6 (q=5) / 8 (q=7). apsp checks simple, bipartite, connected,
max degree <= d.

Rule status from the JSON (check_rule.py): rule graphs have no violations; break4 violates the rule on the two arcs
(4,0), (4,1) for line 16; break2 violates it on arc (2,3).

Reproduce:
  cd research/squads/gqd5-r3/c4
  python3 mk_in.py 5 in_W5.txt && ./relaxed in_W5.txt 28 1 60 T5_s1.txt        (the set T5_s1.txt is given)
  python3 build.py 5 T5_s1.txt rule_s1 rule 1      (modes: rule | break4 | break2)
  ../../../theorems/d5gq/apsp rule_s1.edges 8 5     -> RESULT VALID d=8 D=5 n=1610
  python3 build.py 5 T5_s1.txt break4_s1 break4 1 ; ../../../theorems/d5gq/apsp break4_s1.edges 8 5  -> INVALID
  python3 build.py 7 T7_s1.txt rule7_s1 rule 1     -> VALID d=10 D=5 n=4086

Verdict. (1) VALID at q = 5 and q = 7. (2) Breaking the A-hub rule for one partnered line (its A-hub's D-level slot moved
to a point off the partner) gives diameter 6, at q = 5 and at q = 7, for either D-level slot. Score = 1.
Limits: the relaxed sets are not optimal (23 vs bound 28 at q = 5; 41 vs 53 at q = 7); only the rule-check for one line
was broken, not every line at once (the expected failure is a set of pairs, not all of them).
