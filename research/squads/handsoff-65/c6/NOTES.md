# c6 notes (Haar graph + twisted matching)
Family: vertices a_x (x<m), b_y (m+y), m=|G|. Edges a_x~b_{x s_i} (i=1..5) and a_x~b_{sigma(x)} for an arbitrary
permutation sigma of G (sigma = phi(x) t, so every twisted matching is in the family). sigma = x t gives the Haar graph.
Tool: tw.c (SA over sigma swaps and S changes, full bit-parallel BFS cost = unordered pairs at distance > 5).

## 15:45-16:20 log
- tw.c: SA over (S = 5 translations [+ 6th element T as twist in MODE=haar], sigma = arbitrary permutation swaps in gen mode).
  Options: key=value (MODE=haar|gen, INIT=haar|random, S=a,b,c,d,e,f, T0, T1, IPC, RESTART=random, PSDEN). Cost = unordered bad pairs.
- Scorer checked: tw cost == score65 on its output; mcos S={113,16,280,65,59,295} on sg_342_12 (=C6xC19:C3) gives bad 0 (684 Haar).
- Random 6-regular bipartite on 684 vertices: bad ~ 11-12k (score65). General-sigma SA from random: ~3500 after 60 s.
- Haar-mode SA (6 translations) on sg_342_12: plateaus at 684 bad (random restarts, 150-800k evals); mcos "1|1" finds 0 in 41 s,
  so the plain SA is weaker than mcos on the Haar landscape (mcos uses conjugacy-class-restricted S and per-rep cost).
- Timing: eval ~0.1 ms at n=686. Foreground Bash must pass timeout=600000 for runs longer than ~100 s.
- Groups: tabs made with GAP (7 s for order 343). sg_342_12 = C6 x (C19 : C3); sg_343_{1..5}.
- 16:00-16:25: general twisted SA (tw, gen mode) from random or Haar start on order 342/343: stuck at 3000+ (random start) and 1372 (from best Haar).
  mcos "1|1" on order 343 group 4 (C49:C7): best Haar = 8 rep-violations = 1372 bad at n=686 (25 s). Twisted SA from that start: no gain.
- tabu over S and sigma swaps (tw TABU=1): steepest moves are all worse than current; best 1368 at 342. Not productive.
- phi.c (phi_bin): twisted graph sigma(x)=phi(x) t with phi an automorphism (GAP sample in phi/aut_343_*.txt, autos.g);
  K=Fix(phi) symmetric evaluation via orbit representatives (cost = |K|*(2 nr n - sum pop)/2). Calibration: phi=id gives 1026 at 684 in 40 s (weak SA).
- 16:20-16:40 findings (all n = 2|G|):
  * Haar floor (mcos "1|1", the only zero-capable Haar tool): 360_53 (n=720): bad 360 (2 rep-violations; 40 s run gave 720).
    343_4 (n=686): bad 1372. Haar 360_53 is a strict local minimum: every single translation or swap change adds ~+1000 bad.
  * Twisted sigma = phi(x) t, phi in Aut(G) (300-sample, GAP autos.g), exhaustive over (phi, t) with S fixed
    (phi.c SCAN=1): for 360_53 and for each 5-subset of the floor S6, the best is always the identity (= Haar). No automorphism
    twist beats the Haar floor. Anti-automorphism twists (phi = inv o alpha): best 10035.
  * Random restart SA / steepest-tabu on (S, t) with symmetric cost (phi.c): best ~2900-3200 at n=720 (K up to 90).
  * General sigma (tw gen): ~3000 at n=686 and n=720 (random sigma ~11000).
  * Pool restriction to elements of order 3,6 gives non-simple (multi-edge) graphs; not useful.
- pipe.sh ORDER IDX SECS: mcos Haar floor, then exhaustive automorphism-twist scan for each 5-subset of the floor S6.
