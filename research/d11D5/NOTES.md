# (Δ, D) = (11, 5): notes of job "cell-11-5" (Oct 24–25, 2026)

Record when this job resumed: **7,020** = Z₆ lift of W(8) + doubled matching (research/d10D7/DM_D5.md, coordinator
check Oct 24 16:05 PT). Table value 5,850 (DS14v2); Moore bound 22,222. The first session of this job
(session_01VNcwNF5hUEgWNWcp1VTPhX) was searching for the same 7,020 construction with a δ-invariant ν and a polarity
(stuck at 3 violations). That work is superseded; its tools are kept in this folder (pcover.py, dcover.py, phi*.c).

## Tools (this folder)

- `liftcheck.c`: exact diameter check of a Z_M voltage lift of a bipartite base (BFS from the base vertices).
- `mkbase.py` + `zcons.c`: exact constraint extraction for lifts by G = (Z_K quotient)·Z₂ of W(q) + two parallel
  copies of a duality matching. For each (source, target, coset) it merges the walks of length ≤ 5 by
  (constant, variable set). One class means FATAL, two classes give a GF(2) equation, three or more give an
  OR-constraint. Gaussian elimination decides consistency. On the 7,020 construction (K = 3, copies 1 and 4) it
  reproduces the DM theorem exactly: no fatal groups, no equations, 599,040 OR-constraints (the geodesic parity
  condition), and a random ν violates 2,330 ≈ 599,040/256 of them.
- `z3/zcov.c`: Z_a covering cocycles on W(q). Cost = missing values over all opposite point and line pairs; it
  can anneal or just score. SIGMA=file exempts the pairs that a tripled matching covers by itself.
- `z3/zsat.py`: the same condition as an exact SAT problem (pysat, CaDiCaL).
- `del/farcount.c`: far-pair count of an explicit graph (bit-parallel BFS).

## Results

1. **Order-8 lifts of W(8) + doubled polarity are impossible** (Z₈ and Z₄ × Z₂, jump copies 1 and 2, every
   choice of free Z₂ voltages on flags and on jump edges). The coset ±1 classes of opposite pairs have exactly two
   walks, so they give 1,181,440 GF(2) equations, and these are inconsistent. A minimal contradiction uses 3
   equations. Every duality δ creates the 6-cycles x → δ(x) → δ(l) → δ(y) → y → l → x for points x, y on a line l.
   The equations require all three cycles C(x,y), C(y,z), C(x,z) of three points on one line to be odd, but these
   three cycles sum to zero. The same holds for any duality (W(q) is self-dual for even q), and with a non-duality σ
   the walk counts are Poisson, which leaves pairs with one walk. (runs/zcons_w8_*.log)
2. **The tripled matching over Z₉** (W(q) + 3 parallel copies, flag voltages 3ν, copies 1, 4, 7) has diameter ≤ 5
   iff ν is a Z₃-covering cocycle: the q+1 geodesics of every opposite point pair and line pair carry all three
   values, apart from the pairs exempted by σ. Checked: the Foster cocycle on W(2) gives liftcheck VALID for random
   σ. W(7) would give 7,200 at (11,5), and the same cocycles on W(5), W(8), W(9), W(11) would give records at (9,5),
   (12,5), (13,5), (15,5). But **W(3) has no Z₃-covering cocycle** (SAT UNSAT, also for point pairs alone), W(4) is
   undecided (SAT timeout after 20 min), and annealing on W(7) only goes from 15,861 to 8,781. Counting predicts
   none for random-like ν. A cocycle invariant under all of Sp(4,q) makes all geodesics equal for q ≥ 4, because
   the pair stabiliser is 2-transitive and perfect on the hyperbolic line.
3. **Deleting a perfect matching from the (12,5) chart lift (8,748)** leaves 3.3–3.9 M far ordered pairs (about
   4.5%) for every letter and scalar tried. No slack. (runs/del8748.log)
4. **Counting in the GQ + parallel-jump family.** With base W(q) (degree q+1) and p pairs of parallel jump copies,
   the sheets reachable for opposite pairs are 2(2p+1). Geodesics can only cover Z₂ robustly, and two-jump walks of
   length 4 between opposite points do not exist for a duality (rare otherwise). This gives order
   4(2p+1)(q+1)(q²+1) at Δ = q+1+2p. At Δ = 11 the maximum is p = 1, q = 8, i.e. 7,020. Beating it inside this
   family needs geodesics that cover Z₃ (item 2) or a different base.
5. **Squad round r1-d11D5 (8 Haiku cards), all negative.** Algebraic cubic-character cocycles on W(7) score at
   random level (15,503). Invariant cocycles under tori, Singer cycles and Sylow subgroups reach 8,356 at best. Joint
   σ/ν annealing with exemptions reaches 6,154. Mixed chart lifts over F₃ are valid only up to 2,916, and over F₄/F₂
   none is valid. No lift of the 1,782-vertex (11,4) graph can work: 568 of its vertices lie on no 4-cycle, which
   forces ≥ 301,872 far pairs at order 4. Exact walk-count bounds rule out W(5)+5/Z23, W(4)+6/Z42 and W(3)+7/Z88.
   Every one of the 38,610 edges of the 7,020 graph is critical. (research/squads/r1-d11D5/scoreboard.jsonl)

## The open lead: doubled-matching lifts over NON-quadrangle bases

The DM theorem does not need a generalized quadrangle. For any bipartite base B (9-regular, n points, n lines)
with a point→line bijection σ whose edges are doubled (Z₆ voltages 1 and 4, base flags 3ν), the classes of the lift
are as follows:
- a class reached by a walk that uses a jump gets both Z₂ sheets for free (switch the copy at one jump);
- coset ±1 classes always contain a jump, so they only need reachability in the Z₃ quotient, i.e. a walk of length ≤ 5;
- coset 0 needs pure distance ≤ 2 (then a 2-cycle is inserted), or a jumped zero-sum walk
  (x→σ(x)→·→σ(y)→y, i.e. σ(x), σ(y) concurrent), or ≥ 2 pure geodesics, which leave a parity OR-constraint on ν.
So `plus/plusopt*.c` scores a base by the number of (source, target, coset) triples that fail these structural
conditions (bit-parallel, 4 ms per evaluation, checked against zcons). It anneals σ and degree-preserving flag swaps.
A base with cost 0 then needs ν for the OR-constraints (`plus/orsolve.c`, simulated annealing). The lift has
12n vertices.

W(8) itself (n = 585) scores 0. **One extra pair (n = 586, lift 7,032)** is made by a 9-flag switch: flags
(p_i, L_i) become (x*, L_i) and (p_i, l*). The spread-type switch starts at 2,496, and annealing brings that down to 38, 6, 4, and
then **2** in several independent runs. The last failure is always a single same-side pair at pure distance 4 with one
geodesic and no σ-concurrency (a line pair in most runs). None of the following removes it: single σ-swaps, two-step
σ-swaps, all single flag swaps near the pair, or a penalty on the number of "demand" pairs.
The polarity-symmetric switch (9 absolute points of the Suzuki–Tits ovoid) starts lower (≈1,620), but its new
point can only reach, in cosets ±1, the points collinear with the 9 chosen ovoid points. A 9-subset of the ovoid
does not meet every circle of the inversive plane.

### Structure of the one-pair switch (spread type, σ = δ to start)

- The switch makes the 72 line pairs (L_i, m ∋ p_i) and the 72 point pairs (p_i, z ∈ L_i \ p_i) single-geodesic.
  These "demands" need σ⁻¹(L_i) ~ σ⁻¹(m) and σ(p_i) ~ σ(z) (concurrent or collinear). With σ = δ all 144 hold
  automatically: δ maps the lines through p_i to the points of the line δ(p_i), and the points of L_i to the lines
  through δ(L_i). The last failure in every annealed run was one of these demands.
- With σ = δ, a switch line L_i has no coset +1 walk to the lines meeting δ(p_i). Swapping σ(p_i) ↔ σ(y_i) for some
  y_i ∈ L_i keeps every demand and removes these failures (2,496 → ≈1,450). Swapping σ(δ(L_i)) ↔ σ(δ(m_i)) for a
  line m_i through p_i lets the points collinear with δ(L_i) reach p_i (→ ≈550).
- The new vertices need covering sets. In W(q) every plane of PG(3,q) is a point-perp, so a PG-line blocks all of
  them. Choose L_j = δ(R_j) for the 9 points R_j of a hyperbolic PG-line h. For all 4,160 such h the lines δ(R_j)
  form a regulus with 9 totally isotropic transversals (a 9×9 grid in W(8)), so {δ(L_j)} = h covers x*, and
  {L_j} and {y_j} = (L_j ∩ one transversal) cover l*. Take p_j = L_j ∩ t_{π(j)} for a permutation π. Structured
  starts then cost 122–500 before any annealing (`plus/mkreg.py`, `plus/hline.py`).

### Where the one-pair search stands (end of this session)

- Annealing from many starts (spread switches, regulus switches, polarity switches; σ swaps plus flag swaps; hot-vertex
  targeting; demand-preserving block moves; a demand penalty) reaches structural cost **2** at best, repeatedly
  (best_f5.in, best_g61.in, best_u602.in) and 4 in many runs. A cost-2 state has one same-side pair left: either a
  demand pair (L_i, m ∋ p_i) whose σ-preimages are not collinear, or the fibre of x* or l* (cosets ±1 of
  (x*, x*), which need some σ⁻¹(L_i) on a switch line). Squad r2 card c2 tried all pairs of moves around the failing
  pair of best_f5.in (185,814 first moves × the second moves of the 11 best, 752,811 in all), and nothing went below 2.
- Even at structural cost 0 a second stage remains: the flag cocycle ν must satisfy the geodesic parity
  OR-constraints. With σ fixed to the polarity δ, simulated annealing on plain W(8) stalls at 9 violated constraints
  (`plus/orsolve.c`, 900 s). The previous session of this job also stalled at 3 with a polarity and a δ-invariant ν.
  The DM session reached 0 only by annealing σ together with ν (dmfast SWAPP). So a completed +1 base would need joint
  (σ, ν) annealing that keeps the structural cost at 0.
- Counting bound for this family: the coset +1 classes of a point x are covered only by J+3 walks (≤ 585 endpoints)
  and 2+J+1 walks (≤ 648), so n ≤ 1,233 points per side, i.e. order ≤ 14,796. The 7,020 graph uses 47% of that.
- Last runs: from squad r2 c3's best regulus start (cost 68) the annealer again stops at 2 (best_y901.in). The
  remaining failure is a coset-0 point pair (points 341, 562) with one geodesic and no σ-concurrency. The ν check on plain W(8) with σ = δ stays at 9 violated parity
  constraints after about 2,800 s of annealing in total (fin_w8_or*.log).

**Conclusion for this job.** (11,5) stays at 7,020. Within the GQ + parallel-jump family, 7,020 is the maximum at
Δ = 11 (item 4), and the Z₃-covering escape route has no solutions at small q and none found at q = 7. The
non-quadrangle extension is the one route with a real chance: its exact structural cost gets to 2 but not 0 by every
local method tried (annealing, tabu, exhaustive move pairs, σ-CSP). A completion probably needs joint (base, σ, ν)
optimisation or a two-pair design.

## Round 3 (job resume3-cell-11-5, session_018TRrddhVEdN311drmbPpBK, Oct 25 12:15-15:45 PT)

Tools (folder `inc/`):
- `mkinc.py`: the 8-flag "incident" switch (x* on l*; x* on 8 old lines L_i, l* through the 8 removed points p_i and
  x*); NOINC=1 gives the 9-flag switch. In the incident switch every point at distance 4 from x* keeps exactly 8
  geodesics (a geodesic lost through L_i comes back through l*), and only about 25 point pairs and 25 line pairs per
  side become single-geodesic (the 9-flag switch makes 144). With sigma = delta all of them are sigma-covered.
- `anal.py` (failure types), `sg.py` (single-geodesic and far pairs, sigma cover), `far.py` (point-line pairs at
  distance >= 5), `eqcheck.py` (GF(2) consistency of the forced equations from two-geodesic pairs).
- `nujoint.c`: the nu stage on any base: parity pairs (same-side pairs at distance 4, opposite pairs at distance 5,
  with >= 2 pure walks and no sigma route), focused nu flips + sigma swaps by simulated annealing, structural cost kept
  (weight WS). W(8) with sigma = delta: 1,166 violated -> 2 in 150 CPU s. (WMODE, a clause-weighting variant, does not
  work here: one flip touches ~2,000 geodesics, so weights never pay.)
- `z6lift.c`: exact cost of a Z6 lift with arbitrary voltages on every flag and both jump copies (bit-parallel BFS,
  5 ms), plus an annealer and the edge-list export. Checked: the 7,020 solution gives 0, apsp agrees.
- `finish.sh base.in nu out d D`: DM voltages -> z6lift -> edge list -> apsp.c.

Why sigma = delta is rigid. For a vertex v let Lambda(v) be its pencil. Coset +1 from a point s to a point v is
reached by (a) d(sigma(s), v) <= 3, (b) s collinear with a point of sigma^-1(Lambda(v)), or (c) sigma(v) meets
sigma^-1(Lambda(s)). If the base is delta'-symmetric and sigma = delta', (a) and (b) both say d(s, delta'(v)) <= 3 and
(c) only covers collinear pairs, so every point-line pair at distance >= 5 is a failure. A 9-regular base with 586 + 586
vertices has at least 586 such pairs (a line's 3-ball holds at most 585 points). Every 9-point covering set of W(8)
is a PG-line (Bose-Burton; squad c1), so a switched point p_i, whose pencil changes in one line, needs
sigma^-1(l*) = delta(L_i) or route (c): sigma(p_i) = L_i (`routec.py` applies this to all p_i: starts drop 4x,
e.g. 2,496 -> 640, but the single-geodesic pairs lose their sigma cover). With a random-like sigma the routes are
independent and annealing works.

Results:
1. **Structural cost 0 at n = 586** (W(8) + one pair): squad r3 card c2's clause-weighting search
   (research/squads/r3-d11D5/c2/wpo.c) from the r2 cost-2 state best_y901.in, 325 CPU s
   (`inc/runs/w8p1_cost0_c2.in`; 9 old lines changed, sigma = delta on only 7 points). Round r4 card c1 got a second
   one from best_f5.in in under a minute. Simulated annealing, tabu, LNS, parallel tempering and exhaustive move pairs
   all stay at 2 on the same states.
2. **Structural cost 0 at n = 401** (W(7) + one pair, for (10,5)): squad r3 card c4, 7-flag incident switch with the
   random-like sigma of the 4,800 record, plain po7 annealing (`inc/runs/w7p1_cost0.in`).
3. **(11,5) ≥ 7,032**, checked with apsp.c (graphs/d11D5_n7032_CHECK.md). Base: W(8) with one 9-flag switch and
   no other change; sigma random-like (equal to the polarity on 7 points). nu stage: nujoint annealing from a random
   nu (263,462 active parity pairs, about 1,070 violated at random) to 34 in ~200 CPU s, then SIGFIX FIRST=1 (greedy
   sigma swaps that give a violated pair a sigma route, structural cost kept at 0) to 2, then targeted annealing
   (TARGET=1: with probability PS = 0.02 the move is such a sigma swap, accepted by Metropolis) to 0 in 670 moves.
   Plain annealing alone stalled at 5-30 on four runs; the sigma moves aimed at violated pairs are what finish it.
4. Clause weighting is good from cost <= ~20 and bad from cost in the hundreds (weights spread over hundreds of
   triples and the true cost drifts up). Pipeline for one more pair (`inc/pipeline.sh`): po7 annealing (T0 8 -> 0.3)
   to <= 20, a colder second anneal if needed, wpo to 0, then nujoint TARGET=1 from the old nu (the switched flags keep
   their bits), then finish.sh. `inc/addpair.py` adds a pair away from the earlier new vertices (starts ~2,000).
5. **n = 587 is much harder.** A second pair added to the solved 7,032 base (8- and 9-flag switches, SA with T0 3-20,
   91 points near the first pair frozen, wpo with LMAX 4,000) plateaus at 150-230; two pairs at once into W(8)
   (squad r4 c4) at 164. Control: ONE pair added to W(8) with the sigma of the 7,020 record (inc2/t1) goes 1,998 -> 10
   by the same SA in 450 s and -> 0 by wpo in 39 s. So the second pair interferes with the first: every sigma(s) lies
   on the coverage routes of every new vertex (route (a) needs sigma(s) within distance 3 of the new vertex for all s
   outside the cover of its pencil), and the two sets of demands on sigma do not separate.
6. **(10,5) ≥ 4,812** (W(7) + one pair, graphs/d10D5_n4812_CHECK.md, apsp VALID). The first W(7)+1 base (squad r3 c4)
   got stuck at one violated parity pair in several nu runs (every sigma swap that would cover it broke the structure).
   A fresh base made by `inc/pipeline.sh` (addpair kind b on W(7) with the 4,800 sigma, po7 annealing straight to
   structural 0, nujoint TARGET=1 from the 4,800 nu) went to 0 in 160 CPU s. So for ONE pair on W(q) the whole
   pipeline takes about 10 minutes; W(9)+1 ((12,5) 9,852) and W(11)+1 ((14,5) 17,580) were started at the end.
7. **(12,5) ≥ 9,852** (W(9) + one pair, graphs/d12D5_n9852_CHECK.md, apsp VALID), by the same pipeline: po7 2,924 -> 32,
   colder po7 -> 16, wpo -> 0 (168 s), nujoint TARGET from the 9,840 nu 113 -> 0 (33 s). W(11) + one pair ((14,5)
   17,580) reached structural cost 118 (1,700 CPU s anneal, wq/run/W11L.in; one evaluation takes 10 ms there), not
   low enough for wpo. Extra n = 587 anneals of 1,100 s ended at 160 and 216.


## Round 4 (job resume4-cell-11-5, session_01YVUXzZUE2Fjy42D4zug9Gh, Oct 25-26)

### sigma = delta o C

Let delta be the polarity of W(8) and C a collineation of PG(3,8) outside PGammaSp(4,8). Put sigma(s) = delta(C(s)).
Then sigma^-1(pencil of v) = C^-1(points of the W-line delta(v)) is a PG-line of PG(3,8), and every PG-line is a covering
set of W(8) (a point x is collinear with the point where the plane x^perp meets the line). So route (b) of the coset +1
condition holds for every pair, independently of route (a). If C were symplectic, sigma would be a duality and (a), (b)
would coincide (the rigidity of sigma = delta, round 3). sigma-concurrency of two points means collinearity in the
twisted quadrangle W' = C^-1(W), and the coset-0 demands of a switch become conditions on C:
- (i) the switch lines L_i must stay totally isotropic under C (then sigma(p_i) meets sigma(z) for z in L_i);
- (ii) C^-1(delta(p_i)) must be a W-line (then sigma^-1(L_i) is collinear with sigma^-1(m) for the lines m through p_i);
- (iii) for the new point: sigma^-1(pencil of x*) should be a PG-line, which holds when L_i = delta(R_i) for the points
  R_i of a hyperbolic line h ("regulus switch").
C(W) and W meet in a linear congruence; a regulus delta(h) inside it forces the parabolic type (all W-lines meeting an
axis, which is a transversal of the regulus). Random C with (i) for three switch lines find exactly these (73 lines kept).

Effect on the structural cost (plusopt7):
- W(8) itself: 0 for every C tried. Switched bases: every failure is local to the switch (x*, l*, L_i, p_i).
- One pair: spread switch with sigma = delta 2,496, random sigma ~2,300, delta o C ~800; 9-flag regulus switch with
  (i)-(iii) (dc/mkdc.py) 426-602; incident regulus switch (dc/mkdc2.py: 8 regulus lines, the omitted point R_9 gives
  sigma(C^-1(R_9)) = l* and sigma(x*) = delta(R_9)) 236-302, and then every coset-0 demand and every point-side
  condition holds; what is left is coset +1 from l* and from the L_i to other lines (line side).
- Two pairs (mkdc2.py KS=2: the second hyperbolic line in the plane delta(axis)^perp, so one C keeps both switches'
  lines isotropic): 604-1,310 (earlier two-pair starts: 2,000-5,000).

### What the two-pair search needed (n = 587, 7,044)

- Frozen-bulk annealing (sigma swaps only among ~140-250 points near the switches, rest kept at delta o C) stalls at
  ~100 (one pair) and ~400 (two pairs); the penalised annealer po7R (REF sigma, LAM per deviating point) trades
  structure for cost (squad c2: LAM 2 keeps 2/3 of sigma but stalls at 144). So the structure is a start, not an
  invariant: every successful run moves 300-500 sigma values.
- Two incident regulus switches under one C (dc/mkdc2.py KS=2, start 604): po7 900 s -> 52 (below the round-3
  plateau of 150-230), cold anneal stays at 48.
- **K22 switch** (squad r5 card c8, research/squads/r5-d11D5/c8/k22.py): new points x*, y* both on new lines l*, m*;
  x* on 7 old lines delta(R), R in a hyperbolic line h1, y* on 7 from h2; the 14 removed points split 7/7 onto l*, m*;
  sigma = delta o C, with sigma(C^-1(Ra)) = l*, sigma(x*) = delta(Ra) for an omitted point Ra of h1 (and the same for
  y*, m*, h2). Start 414 -> po7 18 -> cold po7 12 (two seeds, the same 6 conditions: three coset-0 demands and three
  coset +-1 line pairs around l*, m*) -> wpo with LMAX 3000, DECAY 10: 8, 2 (the demand (switch line 104, old line 532
  through its moved point 250)), 0 -> nujoint TARGET=1 from a random nu: 0 violated in 89 s -> 7,044, apsp VALID.
  wpo with the default LMAX 500 drifts up from 12-18 and never improves; LMAX 3000 with DECAY 10 found 8 in 59 s.
- Where the K22 helps: both new points are on both new lines, so the new vertices are pairwise within distance 2;
  with two separate switches they are far apart and their coverage demands on sigma do not overlap.

### Point side versus line side (why more pairs are hard)

For a new point X the coverage of the point side is clean when sigma^-1(pencil of X) is a PG-line (a covering set);
for a new line N the line side is clean when sigma(points of N) = delta(C(PG-line)). With sigma = delta o C both are
geometric conditions:
- point side: X on old lines delta(R), R on a hyperbolic line h, and sigma^-1 of the new lines through X also C^-1 of
  points of h. In a cycle block (X_j on N_j, N_{j-1}) this holds for EVERY new point when the lines h_j form a polygon
  with sigma^-1(N_j) = C^-1(h_j meet h_{j+1}); for a triangle in the plane S of a parabolic C every switch line also
  stays isotropic (dc/tri.py). K22 cannot have it for both points (it would need h1 = h2); the 7,044 start had h1, h2
  meeting in one point, which gives it for x* and 8 of 9 for y*.
- line side: the moved points of N on a hyperbolic line g (squad r5 c5's design). But each moved point must sit on its
  own switch line, and a hyperbolic line meets at most 2 lines of a regulus delta(h). So a block cannot be clean on
  both sides; the annealer has to repair one side. Triangle starts (point side clean): 638-1,208 at n = 588; the
  failures are then the coset +-1 conditions from the new lines (tri.py); forcing moved points onto the next side of
  the triangle (tri2.py) makes it much worse (1,550+).
