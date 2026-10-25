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
  remaining pair is again a coset-0 line pair. The ν check on plain W(8) with σ = δ stays at 9 violated parity
  constraints after about 2,800 s of annealing in total (fin_w8_or*.log).

**Conclusion for this job.** (11,5) stays at 7,020. Within the GQ + parallel-jump family, 7,020 is the maximum at
Δ = 11 (item 4), and the Z₃-covering escape route has no solutions at small q and none found at q = 7. The
non-quadrangle extension is the one route with a real chance: its exact structural cost gets to 2 but not 0 by every
local method tried (annealing, tabu, exhaustive move pairs, σ-CSP). A completion probably needs joint (base, σ, ν)
optimisation or a two-pair design.
