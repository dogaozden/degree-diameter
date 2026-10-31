# selfdual-hi: self-dual (bipartite Cayley) Haar graphs at diameters 7 and 8

Job "selfdual-hi" (Opus cloud session, Oct 31 2026). Method of `../selfdual-d5/README.md` and `../d75-raise/README.md`,
taken from D = 5 to D = 7 and 8 with formula-only groups (no GAP).

## Result

**No record.** No self-dual Haar graph beats any of the six targets ((5,7) 3,120, (6,7) 8,880, (8,7) 43,344,
(5,8) 9,760, (6,8) 31,680, (7,8) 95,760). The method does not transfer from D = 5 to D = 7, 8 in the groups that
hold these cells. The reason is measured below (`Status`): a self-dual S has more coinciding words than a random S,
at a rate set by the commuting probability of G, and at D = 7, 8 that loss outweighs the halved test. Closest:
(5,8) on SL(2,17) (N = 4,896, 9,792 vertices, just above the record): self-dual families best 6 uncovered (3 missed
psi-pairs) after 3.2e7 evaluations, plain annealing best 3 after 2.9e7. Every claim below has its log under `logs/`.

## The test at diameter D

H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B). X = S^-1 S. If psi(S) = S for psi(x) = u0 beta(x)^-1 (beta in
Aut(G), u0 in G), then (g,A) -> (u0 beta(g), B), (h,B) -> (beta(h), A) is a side-swapping automorphism, and the graph
is vertex-transitive. So the diameter is <= D iff the ball of radius D-1 around (e,A) covers the side of parity D-1:

- D = 2k+1 (D = 7): X^k = G. Side B (Y^k = G) follows from the swap; a plain Haar graph needs both.
- D = 2k (D = 8): S X^(k-1) = G. This single condition already suffices for every Haar graph (X^k and Y^k follow
  from it), so at even D self-duality does not remove a condition; it makes S X^(k-1) psi-invariant, so the
  uncovered elements come in psi-orbits.

psi need not be an involution: S is a union of <psi>-orbits; psi has even order 2j and psi^2 is an order-j
automorphism-like map, so j > 1 combines self-duality with orbit-symmetric S (research/structured/STRUCTURE.md).

## Tools (src/)

| file | what it does | calibration |
|---|---|---|
| `sdhi.c` | groups Q1 x Q2 from formulas (SL/PSL/PGL(2,q), q = p^e <= 64; metacyclic C_m : C_k; Z_n); psi options per factor (involutions modulo inner automorphisms; ORDS for higher orders); types = partitions of K into orbit lengths; tabu inside the family (energy = uncovered vertices of the side of parity D-1 within distance D-1 of (e,A)), ENUM=1 exhaustive enumeration with fast rejection and normalisation by the automorphisms commuting with psi; every hit gets a full BFS from (e,A) and (e,B). Header comment has every option. | D = 5, K = 7 on C41 : C16 (the 1,312 group): the tabu finds valid self-dual sets in 1.8 s; ENUM gives the same 202,625,280 sets / 320 solutions as the first version. D = 7, K = 5: PGL(2,5) x Z11 (2,640 vertices) and SL(2,5) x Z10 have self-dual solutions; builder and apsp agree. |
| `build_sdhi.py` | independent builder from the printed formula (own field, matrix and metacyclic arithmetic), same vertex numbering as sdhi's EDGES; BFS from (e,A) and (e,B); compares edge lists | identical edge lists on the probe solutions |
| `haar_sd.c` | research/structured/haar_sym.c plus SDUAL="QOPT U Z0": the same annealer and bitset BFS with S a union of psi-orbits (QOPT inv, ninv, tw, ntw, cinv, meta:A:V:I0:J0; z -> Z0 - U z), one-sided cost at odd D, fixed generators other than e when psi(e) != e or SDNOE=1; the two-sided full check before a solution is written is unchanged. 30-50x faster than sdhi's tabu at N ~ 5,000-20,000 | C61:C80 psi3 type 1+2+2: best 6, the same as sdhi's exhaustive enumeration of that family |
| `hsd_queue.py` | queue of haar_sd jobs, P at a time | |
| `meta_list.py` | metacyclic groups of an order range, one r per cyclic subgroup <r>, with involution counts | |
| `sweep.py` | parallel driver: one sdhi run per group, `summary.txt`, `SOLS.txt` | |
| `sdhi` RANDS=n | energy and mean ball sizes \|X^j\| of n random sets per psi/type (with PLAIN=1 also of plain random S): the distinctness diagnostic below | |

Checks of every hit: research/lifts/coordinator_check/apsp.c (`src/apsp`), VALID at D and INVALID at D-1.

## Status (running log)

- (5,7), K = 5. The record S (PGL(2,5) x Z13, 3,120) is not self-dual for any psi of that group (SDTEST: no
  b S a^-1 is psi-invariant). The self-dual family of PGL(2,5) x Z13 has no solution: every type enumerated
  exhaustively (`logs/K5D7/enum_pgl5_13.txt`) except psi1 type 1+1+1+1+1 (3e8 of its 3.2e9 sets). Frontier probe
  (`logs/K5D7/probe/summary.txt`): self-dual solutions at N = 1,200 (PGL(2,5) x Z10, SL(2,5) x Z10, A5 x Z20) and
  N = 1,320 (PGL(2,5) x Z11, SL(2,5) x Z11), none at 1,440 (best 2-4) or 1,560 (best 4). So in these groups the
  self-dual frontier lies below the plain record. Counting explains it: at K = 5 the self-dual family has about
  N^2 sets with a one-sided success probability p, the plain one about N^4 sets with p^2, so the expected numbers of
  solutions are comparable and plain annealing already searches the plain family well. Metacyclic groups of order
  1,564 with inner psi: 180-300 uncovered.
- (8,7) and (6,7): head-to-head on the record groups against orbit-symmetric S (research/structured/haar_sym, k = 3):
  | group | orbit k = 3 (haar_sym) | self-dual involution families |
  |---|---|---|
  | SL(2,8) x Z43, K = 8 | solved, 11,961 evals (0.4 s) | sdhi tabu 2+2+2+2: best 30 after 211k evals; haar_sd (f = 0, 4 pairs): best 23 after 3.0M evals; f = 2: best 921 |
  | SL(2,5) x Z37, K = 6 | solved, 2,801 evals | haar_sd, 3 pairs, after 9.5M evals each: inv best 84, inv with z -> z best 622, -x^-1 best 80, twisted best 39 |
  | SL(2,8) x Z43, psi of order 6 (self-dual + order-3 symmetry) | | the whole family is 240 sets up to symmetry; best 168 |
  At D = 7 in SL/PGL(2,q) x Z_n the self-dual involution families are far worse than k = 3 orbits. Exponent
  bookkeeping: a self-dual set removes one of the two odd-D conditions (about mu/2), k = 3 orbits divide the misses
  of each side by 3; psi of order 6 would give mu/3 on one side but the family is tiny for K <= 8.
- Structural trap: when beta is inner, H(G,S) is a double cover of a Cayley graph of G; if moreover e is in S the
  central involution in the connection set only adds a perfect matching, and the ball grows like a degree-(K-1)
  Cayley graph (for K = 5, D = 8: at most 4,373 vertices of the target side within distance 7, fewer than 4,880).
  So psi = inversion with e in S is hopeless (haar_sd: best 921-1,990). Families with e not in S or an outer beta
  are the meaningful ones.
- (5,8), K = 5, record group C61:C80 (r = 8, 9,760): the record S is not self-dual. Best self-dual family: PSI 3
  (beta(x) = x, beta(y) = y^41, u0 = y^20, e not in S), type 1+2+2: exhaustive enumeration of all 22,629,048 sets
  (up to the automorphisms commuting with psi), best 6, no solution (`logs/K5D8/enum_meta61_80_8_psi3.txt`); PSI 1
  (u0 = y^20, beta = id) best 320 (`..._psi1.txt`).
- Why self-dual sets lose: they have fewer distinct words. Mean ball sizes of random sets (`sdhi RANDS`, side A):
  | group, (K,D) | plain \|X^2\| / \|X^3\| | best self-dual family \|X^2\| / \|X^3\| |
  |---|---|---|
  | C41:C16, (7,5) (where the method worked) | 577 / - | 538 / - |
  | SL(2,5) x Z37, (6,7) | 660 / 4,110 | 576 / 3,397 (other psi down to 434 / 2,062) |
  | C61:C80, (5,8) | 324 / 2,948 | 308 / 2,451 |
  | SL(2,17), (5,8) | 317 / 3,011 | 307 / 2,855 |
  Counting colliding length-4 words in SL(2,5) x Z37 (30 random sets, `psi(x) = x^-1`): plain 114, self-dual 264
  of 750. The extra collisions are commutation patterns: for S = {s, psi(s), t, psi(t), ..} words such as
  s^-1 psi(s) t^-1 psi(t) and t^-1 psi(t) s^-1 psi(s) are both reduced words of the same length, and they coincide
  whenever two short products commute, which happens with the commuting probability of G (9/120 = 7.5 % for
  SL(2,5), any cyclic factor commutes). So self-dual families want groups with a low commuting probability:
  SL(2,17) (20/4,896 = 0.4 %) loses only 5 % of the words at distance 6, C61:C80 (92/4,880 = 1.9 %) 17 %,
  SL(2,5) x Z37 up to 50 %.
- (5,7) in SL(2,7) x Z4 (N = 1,344): 1,903 self-dual solutions, all with u0 = -I (psi(x) = -x^-1 or
  -(hxh)^-1 on SL(2,7)), mostly type 1+1+1+2 (`logs/K5D7/lowcomm/`); PGL(2,7) x Z4: none (best 3), PSL(2,7) x Z9
  (1,512): none (best 2). Above the record, N = 1,680: SL(2,7) x Z5 with those psi, types 1+2+2 and (psi3) 1+1+1+2
  enumerated exhaustively, the rest tabu 120 s: no solution, best 8 (`logs/K5D7/sl7x5/`); PSL(2,7) x Z10 best 5.
  (5,7) is closed for this method: the self-dual frontier in every family tried lies at or below N = 1,344.
- (6,8): calibration on the record group PSL(2,11) x Z24 with the twisted psi (haar_sd, three psi-pairs): best 7
  after 1.6e7 evaluations, so the family does not even reach the record order (`logs/K6D8/cal_psl11_24_tw.log`).
  Distinctness: PSL(2,11) x Z25 best self-dual family |X^3| 8,983 against 10,873 plain. Closed.
- (5,8) on SL(2,17), PGL(2,17), PSL(2,17) x Z2 (order 4,896, 9,792 vertices; commuting probability 0.4 % for
  SL(2,17)). The best family, psi(x) = -(hxh)^-1 (outer, u0 = -I), keeps 98 % of the distinct words at distance 6.
  haar_sd (`logs/K5D8/hsd/`), 600-1,200 s per run: types 1+1+1+2 and 1+2+2 with psi = -x^-1 and -(hxh)^-1, 3.2-4.5e7
  evaluations each: best 6 (three missed psi-pairs); sdhi tabu (`logs/K5D8/tabu_*.txt`): best 6 (PSL(2,17) x Z2:
  13+, PGL(2,17): 16+). Exhaustive enumeration (sdhi ENUM=1, up to the automorphisms commuting with psi, every set
  checked by fast rejection and the near misses by the exact energy): psi(x) = -(hxh)^-1, type 1+2+2: all
  95,545,984 sets, best 7, no solution (`logs/K5D8/enum_sl17_psi3_t122.txt`); psi(x) = -x^-1, type 1+2+2:
  6,317,676 sets, best 10; type 1+1+1+2: 42,558,480 sets, best 9; no solution (`enum_sl17_psi1_*.txt`). So the
  best self-dual families of SL(2,17) have no (5,8) graph. Control, plain annealing (haar_sym without symmetry) on
  the same groups: SL(2,17) best 1 (10 seeds of 600-1,800 s, 7e7 to 2.4e8 evaluations each; final bests
  2, 1, 2, 1, 1, 1, 3, 2, 1, 3; none reached 0), PGL(2,17) best 13, PSL(2,17) x Z2 best 12. A plain near miss leaves generic elements uncovered (sdhi
  SHOWBEST: 5 elements, none central). So SL(2,17) is the closest group found to a (5,8) graph above the record;
  plain sets get within one element, self-dual sets are exhausted without a solution.

- Squad round sdhi-r1 (8 Haiku cards, `../squads/sdhi-r1/cards.md`): (5,8) metacyclic and product groups, deep tabu
  near the record shape, haar_sd at (6,8) and (7,8), (5,7) metacyclic, a wildcard.

## What is left open

- (5,8) on SL(2,17) with plain sets: best 1 uncovered in 5 of 10 seeds (up to 2.4e8 evaluations), never 0. Longer plain
  annealing there is the most direct chance at a (5,8) graph above 9,760 (not a self-dual one: those are exhausted
  in the main types; the self-dual types 1+1+1+1+1 and psi3 1+1+1+2 (5e8 sets) were only sampled).
- The diagnosis says where self-duality can still pay at D = 7, 8: groups with a very low commuting probability
  (a large simple factor, no cyclic factor) and small valency K (5), where orbit-symmetric S do not fit. Groups
  of the right orders are scarce near the targets (SL(2,17) for (5,8); none for (5,7) between 1,561 and 1,680).
- At K >= 12 the combination with orbit symmetry (psi of order 6, ORDS=6) gets families with two or more free
  6-orbits; at even D its misses come in clumps of 6. None of our targets has K that large.

