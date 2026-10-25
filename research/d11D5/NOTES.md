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
