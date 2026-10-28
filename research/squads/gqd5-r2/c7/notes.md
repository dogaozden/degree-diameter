# r2c7: full-graph test of the relaxed-pair rule (fact 12), q = 5, r = 2, types HHDHD

Setup. G = Q(4,5) = W(5).dual(). Five levels, rotational tournament j -> j+1, j+2 (mod 5); types H H D H D.
Arcs: H->D 0->2, 1->2, 3->4 free the ovoid O (26 points, regular spread of W(5)).
D->H 2->3, 4->0, 4->1 free the relaxed set T (lines of Q(4,5)).
Non-friendly 0->1, 1->3, 3->0, 2->4: index bijection, nothing freed (LD=1: a 2-point local duality on each, from localdual.py).
Hubs: B-hubs take one A-slot per level, A-hubs one B-slot per level. Slots are chosen by a SAT model (python-sat, Cadical);
with rule=1 the RELAXED-PAIR RULE is imposed as clauses (partnered line l with partner m: the B-hub's slot in the target
H-level is O∩m; the A-hub's slot in the source D-level is the B-slot at O∩m). Hub graph Y (degree 3, max = q-r) annealed
by research/theorems/d5gq/hubopt.py.

T. relaxed.c on W(5) (flag = joining W-line in the spread, i.e. meeting point on O, forbidden), 40 s, seed 1:
|T| = 23 with 6 concurrent pairs, all meeting points off O (checked in build_rel.py and check_rule.py).
Seeds 2 and 3 reached 20 and 16 at 40 s. A 150 s run for target 26 was killed without output.
Slot caps: alpha = (level 0..4 A-slots) = (28, 28, |T|+2, 28, 46) with LD, beta = (|T|+2, |T|+2, 52, |T|+2, 28);
so K_A = K_B = min(28, |T|+2) = 25 here.

Results (n = 1560 level vertices + K_B + K_A hubs; verdicts from research/theorems/d5gq/apsp EDGES 8 5):
| file | T | LD | rule imposed | check_rule.py | apsp D=5 | apsp D=6 | n |
| norule.edges | 23 | no | no | False | diameter 6, INVALID | VALID | 1606 |
| rule.edges | 23 | no | yes | True | VALID | VALID | 1606 |
| ld23norule.edges | 23 | yes | no | False | diameter 6, INVALID | VALID | 1610 |
| ld23.edges | 23 | yes | yes | True | VALID (d=8, D=5) | VALID | 1610 |

Reading. Same T, same K, same hub-graph search: only the hub slots differ, and the rule alone takes the diameter from 6 to 5.
The record is ld23.edges: n = 1610 = 1560 + 25 + 25, degree <= 8, bipartite, D = 5 (director's no-relaxation version: 1,600).
Reproduce: LD=1 python3 research/squads/gqd5-r2/c7/build_rel.py research/squads/gqd5-r2/c7/T5_1.txt ld23 1 0 1
(arguments: T_file out_prefix rule K seed). Output in ld23.json: T, O, hub slots and Y.

Not done: |T| = 26 would allow K = 28 (n = 1616); the SA reached only 23 at 40 s.
