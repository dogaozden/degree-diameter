# A8 (search wildcard, open): twisted Z11-layer orbits on psl 243 x Z11

Card: research/squads/d11D10-r2/CARDS.md, A8. Target G = PSL(2,243) x Z11, N = 78,917,652, d = 11, D = 10.
Clock: started 12:49:28 UTC, last run finished 13:00:23 UTC. Slot use: about 1.4 slot-min (twisted run), plus the
random-S baseline if it ran (see the baseline section). Budget 8.

## Idea (not in haar_sym's options, not used by the other 15 cards)

Every family so far has S invariant under an automorphism alpha of G (haar_sym's ORBIT). The twisted family
replaces alpha by an affine map. With the code's convention (edges (g,A) ~ (s g,B), so right multiplication by G is
an automorphism):

- Take u, g in PSL(2,243), both of order 11, and z-shift 1. Put
  S = { f^k(e) : k = 0..10 } where f(x,z) = (g x u^-1, z+1),
  i.e. S = { (g^k u^-k, k) : k = 0..10 }, one generator in each Z11 layer.
- phi(x,A) = (u x u^-1, A), phi(y,B) = (g y u^-1, B) maps every edge (g,A)~(s g,B) to an edge iff f(S) = S, which
  holds by construction. phi fixes (e,A).
- f has no fixed points (z shifts by 1), and f^11 = id because g^11 = u^11 = e. So every clump of uncovered B-side
  elements has size exactly 11 and there are no small-orbit (alpha-fixed) misses. Random S would need about
  e^(mu/11) = e^5.5 = 0.4 % of draws to give cost 0.
- Structure: the non-backtracking words of length L are in bijection with the reduced words of Z11 * Z11 in g, u
  (normal forms g^k1 u^(k2-k1) g^(k3-k2) ..., middle exponents nonzero). So all coincidences come from relations of
  <g,u> inside PSL(2,243).

## Implementation

- Copy: research/squads/d11D10-r2/A8/haar_sym_A8.c (haar_sym.c plus one mode, TWISTORB=m, about 70 lines before main;
  the dispatch line sits before the ORBIT line). Built with
  `gcc -O3 -march=native -fopenmp -o haar_sym_A8 haar_sym_A8.c -lm` (warnings only, pre-existing).
- u: random element of order 11 with z = 0 (index 53475433). g: a new random order-11 element (z = 0) per sample.
  D = (g u^-1, z=1). f(y) = D * alpha(y), alpha = conj(u) with AR = 1. Samples with a non-closing orbit are redrawn.
- Command (run through the gate, log twist120.log):
  `env -u THREADS TWISTORB=120 ./haar_sym_A8 11 10 0 1 8 /dev/null psl 243 11`
  (wrapper: run_twist.sh; gate.sh 300 bash run_twist.sh)

## Results: 120 samples, psl 243 x Z11 (twist120.log)

- orbit z-coordinates: 0 1 2 ... 10 (one generator per layer, as designed).
- Symmetry check: all 120 costs are multiples of 11 (0 exceptions). The f-invariance of the uncovered set holds.
- Distribution of the 120 costs: 88 below 1e4, 21 between 1e4 and 1e5, 11 at 1e5 or above (max 1,021,526 = 1.3 % of N,
  others 300,069 and 20,031). min 1870 (170 clumps), median 4917 (447 clumps), 90th percentile 30,877 (2,807 clumps),
  mean 69,765 (pulled up by the 11 large samples). Cost 0 in 0 of 120. Every sample has at least 170 clumps.
- Reference: random S has mu = 60.6 (preamble; Poisson mean lambda = W/N = 14.08). The k = 5 Frobenius RANDORB medians were
  56-71 (preamble). The twisted family's median (4917 uncovered) is about 80 times the random-S mean.
- Median cost 4917 gives an effective lambda = ln(N/4917) = 9.7, against 14.08 for random S (assuming a Poisson model,
  which is an assumption here). Since distinct words are distinct in Z11 * Z11, every coincidence is a relation of <g,u>
  in PSL(2,243). Those relations appear to hit far more words than in random S (inferred, not checked).

## Baseline

Not run. The plain random-S baseline (RANDSAMPLE=20, same binary) was queued behind other cards' slots and
cancelled at 13:05 unrun. Reference instead: the preamble's random-S mu = 60.6 and the k = 5 RANDORB medians (56-71),
from the same cost code path.

## Negative cases and what was not run

- A plain (unsymmetric) anneal, `haar_sym ... psl 243 11` without ORBIT, 240 s, was queued and cancelled before it
  ran. No data.
- The AR = 1 screen (k = 5, Z11 untwisted) was not run.
- Only one u was used. All 120 samples share it, so u-dependence is untested.

## Conclusion

No VALID graph. The twisted Z11-layer family gives a clean symmetry (clumps of 11, verified), but its covering is
much worse than random S (effective lambda about 9.7 vs 14.1). It is not a route to 157.8M. Suggested next step
for anyone with budget: check the loss against other u, and count distinct covered elements per word length, before
spending more on this family.
