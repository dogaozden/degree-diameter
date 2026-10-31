# c13 notes (round 2: continue the surgery lead, symmetric insertion)

## Setup (17:45-18:00)
- g342.txt: SmallGroup(342,12) table (copied from c7/tabs). Only one involution (element 1, central); 116 elements of order 3.
- S = {106,241,112,304,137,24} from `shared/mcos` TYPE=1|1 (SOL line). mkhaar.py builds H(G,S): A_x ~ B_y iff x^-1 y in S
  (A_x = id x, B_y = id 342+y). h684.edges rebuilt: check.sh bad 0, diameter 5.
- Automorphisms: LEFT multiplication by any g in G (x -> gx on both sides) preserves the rule x^-1 y in S.
  It is fixed-point-free, so a pi-invariant graph has an orbit structure.

## Tools written
- mksym.py K GELEM SEED OUTEDGES OUTPERM: symmetric insertion of K vertex pairs (u_i, v_i) into h684, pi = left mult by
  GELEM (order K). Removes 5K edges (5 orbits of pi), attaches the old endpoints to the new vertices by pi-orbits, adds
  u_i v_i. n = 684 + 2K. K=1 gives the plain 686 insertion (5 edges), K=2 gives 688 with Z_2 (GELEM=1), K=3 gives 690
  with Z_3 (GELEM=2). Degrees checked.
- symsa.c / symsa: SA over pi-invariant 2-switches (proposal = switch (e1,e2) and its pi-images, all K applied
  sequentially, validity checked). env: INFILE, PERMFILE, ORD, SEED, ITERS, T0, T1, SECS, PG (guided e1 at far-pair
  endpoints), OUT. Cost: bad pairs (bit-parallel BFS, 0.15 ms per evaluation at n=688).

## Results
- Insertion starts: K=1 random insertion 686: cost after insertion ~600s; K=2 688: 660.
- K=2, 60 s, T0 1.5 T1 0.1: 688 -> 397 (45 s).
- K=1 (plain 2-switch, 90 s, T0 1.0 T1 0.2): 686 -> 237. (c7's guided SA reached 177 with longer runs.)

## Round 2 runs (17:50-18:05)
- Group automorphisms (autg.py): with S fixed, only the identity survives among automorphisms of G = SmallGroup(342,12)
  (generators 69, 292). So H684 has no involution with fixed points from group automorphisms; a fixed-point-free
  Z_2 (left mult by the central involution, element 1) is the only symmetric option for 688.
- Symmetric K=2 (688, Z_2 = left mult by element 1), 270 s, T 3.0 -> 0.5, 1.5M moves: 660 (insertion) -> 384.
  File k2_b.edges (bad 384). Logged on the scoreboard (first 688 line).
- Plain 686 reheats from c7's 177 graph (symsa2, ROUNDS restarts from best, T 2.0 -> 0.3): see run_k1_177.log.

## Runs 18:00-18:12
- 686 reheats from c7's 177 graph (symsa2, restart from best, T 2.0 -> 0.3, 1.4M moves): stays at 177 (run_k1_177.log).
- 686 kicked restarts (symsa3, KICK=25 random switches per restart, T 1.5 -> 0.2): the kick is too strong, the state
  drifts to cost ~2000 and never returns (run_k1_kick.log). Random switches from the 177 graph cost ~+40..+400 each.
- Z_3 symmetric 690 (K=3, pi = left mult by element 2, order 3; ins3_s1.edges -> k3_a.edges): 447 after 230 s,
  1.2M moves, T 3.0 -> 0.5. Logged on the scoreboard (first 690 line).
- Plain (non-symmetric) 688 from the 2-pair insertion (ins2_s1.edges): 403 after 222 s (p688_a.edges). The Z_2
  version (384) is slightly better, so the symmetry does not hurt much.

## Analysis (why surgery on H684 is limited)
- Deleting one edge of H684 creates 44..83 bad pairs (c7 damage numbers). Any 686 made from H684 deletes at least 5 edges
  (6-regular, 2 new vertices need 12 stubs: 5 deletions + 1 new u-v edge). Deletion damage alone is about 5 x 44 = 220 pairs,
  and the 12 new edges repair only part of it. The SA floor is 177 (686), 384 (688 Z_2), 403 (688 plain), 447 (690 Z_3).
- So surgery on H684 is structurally stuck near 170+. Bad 0 at 686 would need a starting graph whose edges are much less
  critical than H684's (its edges are critical because the 4-balls are almost exactly tight).
- Group automorphisms of G preserving S: identity only (autg.py). No fixed-point involution gives a symmetric 686 insertion.

## Runs 18:12-18:30
- Remove-a-pair start (mkpair.py: delete a vertex pair of H684 + 2 extra edges, insert 2 pairs as K22, 686 vertices): start 290,
  plain SA 230 s -> 223 (pair686_a.edges). Not better than the 177 basin.
- Z_2 symmetric 688 continued from 384 (restarts from best, T 1.5 -> 0.2): 384 -> 320 (k2_c.edges). The next restart stays at
  320 (k2_d.edges). New 688 best 320 on the scoreboard.
- Plain 686 from a fresh insertion with PG=0.9 (mostly guided moves): 242 (g686_pg9.edges). Guided-heavy is not better.

## Runs 18:36-19:00 (all single runs, 230 s each, one process at a time)
Plain 686 from fresh random pair insertions (mksym.py K=1 seeds 2,3,4; ins1_s*.edges):
  T 0.8->0.15 (cold, 1.5M moves): 207 (cold686.edges)
  T 1.2->0.25: 182 (mid686_s3.edges)
  T 1.0->0.2: 231 (mid686_s4.edges)
  PG=0.9 (mostly guided): 242 (g686_pg9.edges)
  Fresh insertion, earlier seed 1, T 2.0->0.3: 237 at 90 s; c7 guided SA: 177 (best686_bad177.edges)
Plain 686 from the 177 graph:
  T 1.0->0.1, PG=0.2: 177 (no change, low686_177.edges)
  ILS (KICK=3 random switches per restart, T 0.6->0.15): best stays 177, the kicked state drifts to cost ~440
  (ils686.edges is the current state, not the best). Random switches are very damaging here.
Z_2 688 (k2_b -> k2_c -> k2_d/k2_e): 384 -> 320, then flat at 320 (k2_c.edges is the best 688 Z_2 graph).
Z_3 690 (k3_a -> k3_b -> k3_c): 447 -> 417, then flat at 417 (k3_b.edges is the best 690 Z_3 graph).

## Summary of the card (c13)
- Symmetric insertion (688 with Z_2, 690 with Z_3): done. Best 688 bad 320 (Z_2), best 690 bad 417 (Z_3).
- Plain 686 surgery and ILS: best 177 (the c7 basin). Reheats, kicks, cold/hot schedules, guided fractions: no gain.
- Covering search for new vertices: subsumed by c7's exhaustive 2-opt scan (all 2.05M 2-switches of the 178 graph, min
  increase +6). A depth-2 covering search was not run: its first-level set alone is about 2052 x 12 switches followed by a
  full second level, roughly 2 hours per first move at 0.15 ms per evaluation.
- Remove-a-pair + K22 insertion (pair686_a.edges): 223 at best.
- Verdict: no bad-0 graph with n > 684 in this card. Surgery on H684 floors at about 177 for 686.

## Next ideas (not run)
- Structural: replace H684 by a 686-vertex base that has less critical edges (edge deletion damage of H684 is 44..83).
- Exact covering with 3-switch lookahead restricted to the far-pair vertices (needs a faster BFS: bitset per level is already
  used; incremental update of only the changed balls would be the speedup).

## Stacked 688 (19:00-19:08)
- stack.py: one more vertex pair inserted into the 177 graph (5 matching edges removed): start 469, SA 230 s -> 344
  (stack688_a.edges), restarts -> 327 (stack688_b.edges). Similar to the Z_2 688 (320), not better.

## Final tally (19:23)
- Plain 686 fresh insertions (seeds 1-7, 230 s each, schedules 1.0-2.5 -> 0.15-0.4): best 182, others 189, 191, 207, 218,
  223 (pair start), 231, 237, 242. The c7 177 graph is still the best 686 found. Reheats of 182 and 177: no gain.
- 688: Z_2 symmetric 320 (k2_c.edges), stacked 327 (stack688_b.edges), plain 403, Z_2 384 (k2_b.edges).
- 690: Z_3 symmetric 417 (k3_b.edges), first 447 (k3_a.edges).
- Nothing with bad 0 and n > 684; no CLAIM.
- Last runs (19:27-19:31): 177 graph restarts (T 0.8 -> 0.1): 177 (final686.edges). Z_2 688 restarts (T 1.0 -> 0.15): 320
  (k2_f.edges). No new bests. Stopped at 19:31 because all variants of the card had plateaued; no processes left.
