# B8 (constructions wildcard): routes to (11,10) above 148,729,680 that are not a haar_sym search

Card B8 of squad round d11D10-r2. Start 12:51 UTC, finished inside the 40-minute box. Heavy budget used: 0 slot-min.
All numbers come from pure counting (scripts `routes.py`, `abelian_check.py`, `metacyclic_list.py` in this folder).
No graph was built, so there is no valid graph to score. Score 0.

## Conclusion (negative)

No construction route that avoids a covering search reaches 148.7M in our reach. Every family below either has a
counting ceiling under 148.7M, or needs a covering efficiency that no known family here has. The best certified
number from a non-search route is 63,655,099 (a Delorme blow-up of our (10,10) record; buildable from the existing
(10,10) file, not built, and far below the table's 130,592,354). The only thing that beats 148.7M is a structured search
with mu about 24 at N = 74.4M per side
(haar_sym, k = 5), as the Opus session already has.

## Numbers used

- Bipartite Moore bound for (11,10): per side W = 11(1 + 10^2 + 10^4 + 10^6 + 10^8) = 1,111,111,111, total 2,222,222,222.
  Table 130,592,354 = 5.88 % of it; ours 148,729,680 = 6.69 %; target 157,835,304 = 7.10 %.
- Random-model coverage: mu(N) = N e^(-W/N) per side. mu = 24.1 at N = 74,364,840; mu = 60.6 at 78,917,652;
  mu = 2.66 at 65,296,177 (the table's order). The random-sampling frontier (mu = 1) is N = 61.9M per side,
  i.e. 124M vertices.
- Size law (frontier/SIZE_LAW.md, size_law_fits.csv row "prediction,11,10"): predicted 139.4M (136.2M–142.6M).
  Ours beats it by 6.7 %.

## Route by route

1. **Single-orbit abelian Haar graphs (bi-circulants on Z_N, or any abelian G with |S| = 11).**
   An odd walk of length l <= 9 from (0,A) ends at sum_i c_i s_i with c in Z^11, sum c_i = 1, |c|_1 <= 9. In an abelian
   group the endpoints depend only on c, so the B side has at most #{c} vertices.
   #{c} = **907,753 per side** (1,815,506 vertices total). `abelian_check.py` runs a BFS on random S in Z_N for
   (|S|, D) = (3,6), (4,6), (4,8) with N = 2,000,003. The BFS counts equal the bound exactly (27, 92, 216), so the bound is
   tight. Consequence: a bi-circulant can never reach 130.6M, and the table's graph is not one. Its order
   65,296,177 = 563 * 115979 with 563 | 115978 = 115979 - 1 (both primes) suggests a non-abelian Frobenius group
   Z_115979 x| Z_563 instead. That is a hypothesis only; we do not have the table's file. **Dead** for abelian groups.

2. **Cyclic / multi-fibre lifts of a base graph (voltage lifts).** A lift with base b per side and voltage group Z_n is
   a Haar-type graph over G x Z_n with a structured S. The random-model coverage depends only on the per-side order
   N = b n, so lifts have the same mu(N). Escaping the abelian bound needs b > 1, which only helps through the base's
   non-commutativity. Z_2 lift of our own 148.7M graph (per side 148.7M, lambda 7.47): expected uncovered elements
   **84,710**. Parity check: for a random voltage vector the expected number of base elements whose covering words all
   share one parity is 2N e^(-lambda/2) = 84,700, the same number. Each of the 2^10 voltage vectors (up to a global
   sign) has about 84,700 expected defects, so a defect-free one would be a random event of probability about
   e^(-84,700). **Dead** unless the voltages are chosen by a covering search.

3. **Delorme blow-up (copies of vertices with identical neighbourhoods).** A blow-up G[m] keeps the diameter (distances
   between copies equal distances between originals; checked by the projection argument). It needs
   sum over u in N(v) of m_u <= 11 for all v. For a 10-regular base the copies can go on both sides, each side up to N/10,
   so the best total is 1.1 x n(10,10). Our (10,10) record (`frontier/SIZE_LAW.md`) is 57,868,272, so the blow-up gives
   **63,655,099**. To reach 148.7M the base needs 135.2M, which is 15.5 % of the (10,10) Moore bound 871.7M (ours is 6.6 %).
   For base degree 9 the need is 39.7 % of the (9,10) bound; for 8 and 7 it is above 100 % (impossible). **Dead.**

4. **Cartesian products (degrees a + b = 11, diameters D1 + D2 = 10).** Vertex counts multiply and so do Moore counts.
   The largest product of Moore totals over all splits is K_2 x H with H a (10,9) bipartite graph:
   **193,710,244** as a Moore bound. The odd-diameter bound for (10,9) is per side min(even-ball radius 8, odd-ball radius 9)
   = 48,427,561 (the same-side ball binds), so the total is at most 96,855,122. K_2 x H needs total(H) >= 74,364,840,
   i.e. 76.8 % of that bound. Our best (8,9) record 1,130,880 is 8.4 % of its own bound. **Dead.**

5. **Subgraph of a (12,10) Haar graph (delete one generator).** Our (12,10) record is 310,628,640 (per side 155.3M,
   `SIZE_LAW.md`). An 11-subset S' of its 12 generators has W/N = 7.15 at that order, so the random-model mu is
   **1.2e5**. Only a specially chosen S' could keep diameter 10, and that is a covering search again. **Dead** as a
   route.

6. **Generalized polygons and diameter 8.** There is no generalized 10-gon (Feit-Higman), and generalized octagons of
   degree 11 are not known. A bipartite (11,8) graph has at most 22,222,222 vertices (per side 11,111,111), so no
   diameter-8 family can reach 148.7M. **Dead.**

7. **Other groups (Cayley/Haar graphs of metacyclic or Frobenius groups).** These are the natural non-abelian
   candidates (the non-abelian ones with q >= 3). Orders p*q with q prime, q | p-1, in (74,364,840, 78,917,652]: 130,570 with q = 2 (dihedral), and
   74,646 with 3 <= q < 400 (`metacyclic_list.py`). Each candidate has the same random-model mu(N) as above
   (24 to 61), so a random S succeeds with probability about e^(-24) to e^(-61) under the random model. Reaching these
   orders needs a structured search, which is haar_sym's `meta` option, not a new construction. Not run.

## What the table value says

Random sampling of Haar graphs at N = 65,296,177 has mu = 2.66, so each sample succeeds with probability about 7 %.
That is consistent with (a hypothesis, not checked) the table's Loz graph having been found by sampling a non-abelian
family. The random frontier
(mu = 1) is 61.9M per side. Random sampling cannot reach 148.7M (mu = 24, probability about 4e-11 per sample). The
search that reached 148.7M is structural: k = 5 orbits with ORBW = 5 and 609 evaluations.

## Files

- `routes.py`: all counting bounds above (`python3 routes.py`, under 1 s).
- `abelian_check.py`: BFS check of the abelian bound for small (|S|, D) (`python3 abelian_check.py`).
- `metacyclic_list.py`: primality checks and the list of Frobenius/metacyclic orders in the window (about 2 s).
- No gated runs. No process from this card is still running.
