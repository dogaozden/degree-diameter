# Gómez's ΩH_q with a free labelling (table-audit-2, 2026-10-26)

The six green D = 8 cells (10,8), (11,8), (12,8), (14,8), (15,8), (16,8) are Gómez's ΩH_q (PhD thesis, UPC 1986,
§2.9.3, Fig. 2.21 a/b, p. 43–46) for q = 7, 8, 9, 11, 13. As drawn, with the same row label in every copy, the graph
has diameter 9 (table-audit-1: checks/omega_D8.txt and tools/omega_bound.py; own-12-8: ΩH₉ exactly 9). This folder
asks the next question from the brief: does ANY labelling of the copies give diameter 8?

## Model (omega_model.h)

5α copies of H(q) (blocks of 5, each of type a or b), n = (q⁶−1)/(q−1) rows. Copy c marks one point P_c[t] and one line
L_c[t] per row t (P_c, L_c bijections); in each block one class is "inner" (the pentagram ends) and the other "outer"
(the circle ends). Hubs (t,k), (t,k̄) for k ∈ Z₅:
- type a: (t,k) ~ inner marks of copies k±1, (t,k̄) ~ outer marks of copies k+2, k+3;
- type b: (t,k) ~ outer marks of copies k+3, k+4, (t,k̄) ~ inner marks of copies k±1.

Any labelling gives a bipartite graph of order 5(α+1)|H(q)|, copy vertices of degree q+3, hubs of degree 2α. The
thesis's labelling is P_c[t] = t, L_c[t] = σ(t) for every c. `omega_verify.py` re-derives the wiring from the figure in
Python, independently of the C code.

## What a labelling must do

In every graph tried, all pairs at distance > 8 were hub–copy-vertex pairs at distance exactly 9, with the copy vertex
in a copy the hub does not touch and of the opposite colour (so it needs distance ≤ 7). Copy–copy and hub–hub pairs
were always within 8. A path from hub (t, ℓ) to such a vertex v of copy c′ is either
- one hop: hub → mark of row t in an adjacent copy c₁ → (a steps in c₁) → mark of row t′ for a label ℓ′ shared by c₁
  and c′ → hub (t′, ℓ′) → mark of row t′ in c′ → (b steps) → v, with a + b ≤ 4; or
- two hops with a + b + c ≤ 2.
So for every hub and target copy, about 2α–3α "routes" (c₁, ℓ′) must jointly cover the n opposite-colour vertices of
c′, each route covering at most about 2q⁴ of them.

**Flat labellings cannot work.** If every copy's marking is the base marking moved by an automorphism of H(q) (the
same automorphism on points and lines, i.e. collineation labellings), relabelling each copy by the inverse
automorphism gives back the thesis's same-label graph, so the diameter is 9 (for q ≥ 7 by tools/omega_bound.py, and
checked at q = 2, 3). A labelling has to scramble rows between copies.

**No counting argument rules labellings out.** `ubound.py` (`python3 ubound.py q TYPES INNER`; `ub_all.py` loops over
all patterns) sums, for the worst hub
and target copy, the most each route can cover (sphere sizes of H(q)), over every block pattern and inner-class
choice. The ratio of that sum to n is

| q | α | union bound / n (all patterns about equal) | of which: centre ball, one hop, two hops |
|---|---|---|---|
| 3 | 3 | 9.37 | 0.33, 4.68, 4.35 |
| 4 | 3 | 5.52 | 0.25, 3.44, 1.83 |
| 5 | 4 | 5.62 | 0.20, 3.60, 1.82 |
| 7 | 5 | 4.30 | 0.14, 3.13, 1.02 |
| 8 | 5 | 3.58 (before removing duplicate routes) | |
| 9 | 6 | 3.69 | 0.11, 2.87, 0.71 |
| 13 | 8 | 3.10 | 0.08, 2.60, 0.42 |

(worst hub/target: an unbarred hub and a type-a copy three steps round the pentagon, opposite-colour targets;
identical routes through two labels are counted once.)

It stays above 1 (it tends to about 3 as q grows), so counting alone does not decide the question. It does say how
hard it is: for a random labelling a target is missed with probability about e^(−ratio), which matches what we see
(far pairs per hub source: q = 3 about 6·10⁻⁵ of all pairs, q = 4, 5 about 7·10⁻⁴).

## Searches (omega_symanneal.c)

Labellings equivariant under G = ⟨g⟩, g a Singer-type element of SL(3,q) ≤ G₂(q) acting semiregularly on points and
lines (hex_aut.py: order 13 at q = 3, 7 at q = 4 (the cube of the Singer cycle), 31 at q = 5, 19 at q = 7), so the
graph has G as automorphisms and BFS from orbit representatives decides the diameter. Optionally Z₅ acts too:
- ZMODE=1: the 5 copies of a block identical. Bad: at q = 3 a random labelling has 4,617 far pairs from the 56 hub
  representatives and annealing stalled at 1,823.
- ZMODE=2: copy 5B+i uses the block marking composed with ψ^i, ψ a G-equivariant row permutation of order 5. At q = 3
  a random labelling already has only 34 far pairs, and annealing reaches 0 in about a minute.
- NOZ5: all 5α copies independent.

## Results

- **q = 3 (ΩH₃, 14,560 vertices, 6-regular): diameter 8.** Two labellings (labs/q3_aba_LLL_G13.lab, NOZ5, 162 s;
  labs/q3_aba_LLL_G13_Z5psi.lab, ZMODE=2, 70 s), types aba, inner LLL. Both pass apsp.c (no symmetry assumed) and the
  wiring check (checks/omega_labelled.txt). With table-audit-1's q = 2 result this shows that ΩB₁ can reach D₁ + 2,
  but only with a labelling the thesis does not describe.
- q = 4 (54,600 vertices) and q = 5 (195,300 vertices): **no labelling found.** Twisted-Z₅ × Singer annealing
  (lead, 25–30 min each) and squad round table-audit-2-r1 (8 strategies, about 15 min each) all stayed near the
  random level: q = 4 from 18,387 far pairs (390 hub representatives) to about 12,800–13,900 (one 75-minute run, 253,220
  moves: 12,075); q = 5 from 42,280 (252
  representatives) to about 35,500–38,000. Pattern scan at q = 5: abab LLLL best, aaab clearly worst. Closed-form
  structured families (affine maps on the orbits, identical copies, incidence-matched pairs) are no better than random
  (squad c7). Independent copies (NOZ5) were not better per unit of time.
- q = 7 (1,176,480 vertices, the (10,8) order): a random labelling with the Singer-cube symmetry (order 19, 1,032
  orbits) leaves 6,813,773 far pairs from the 2,064 hub representatives (about 3,300 of 1.18 million per hub). A
  cost evaluation takes about 10 s on this machine, so annealing to 0 is out of reach here.

## First-moment estimate (heuristic, not a proof)

Let F be the number of (hub, vertex) pairs at distance > 8. For a uniformly random labelling (every P_c, L_c an
independent random bijection), E[F] measured here: q = 2 about 70 (twisted-Z₅ random, ×35), q = 3 1,911 (fully random,
all 3,640 hubs), q = 4 645,753 (fully random, all 13,650 hubs; the symmetric random labellings give 643,545),
q = 5 about 6.55 million (symmetric random ×155), q = 7 about 647 million (symmetric random ×95). The number of
labellings, up to a global relabelling of the rows, is (n!)^(10α − 1). If the far pairs behaved like independent
events, P(F = 0) ≈ e^(−E[F]) and the expected number of labellings with diameter 8 would be exp(ln #labellings − E[F]):

| q | ln #labellings | E[F] | exponent | found? |
|---|---:|---:|---:|---|
| 2 | 3.8·10³ | ~70 | +3.7·10³ | yes (round 1) |
| 3 | 5.2·10⁴ | 1.9·10³ | +5.0·10⁴ | yes |
| 4 | 2.5·10⁵ | 6.5·10⁵ | −4.0·10⁵ | no |
| 5 | 1.1·10⁶ | 6.6·10⁶ | −5.4·10⁶ | no |
| 7 | 8.5·10⁶ | 6.5·10⁸ | −6.4·10⁸ | no (not searched to the end) |

So random-like labellings should exist at q ≤ 3 and should not exist at q ≥ 4, which is what the searches saw. This
says nothing about structured labellings (the far pairs are far from independent), so it is not a proof that the
table's D = 8 values have no graph. It agrees with research/frontier/SIZE_LAW.md, where the same kind of
first-moment count puts (10,8), (12,8), (14,8), (16,8) at or above what random Haar graphs can reach.

## Verdict

(See also own-12-8, research/squads/cells/d12D8_table.md on its branch: Theorems 1–2 prove diameter ≥ 9 for the
thesis's labelling under every reading at q ≥ 7, and random relabellings of ΩH₉ leave about 10¹⁰ far pairs.)


For the table's q = 7, 8, 9, 11, 13 the thesis's construction as drawn has diameter 9 (INVALID as read; witness in
checks/witness_omega_thesis.txt). A free relabelling of the copies can repair it at q = 2, 3. Whether some labelling
repairs it at q ≥ 4 is open: no counting argument excludes it, random-like labellings miss a fraction of about
e^(−ratio) of the targets, and local search removes only a third of the misses. A repair at the table's q would need
a structured labelling whose routes nearly tile each copy; none is known.

## Files

omega_model.h (construction), omega_eval.c (exact far-pair count / diameter, any source set, edge-list output),
omega_symanneal.c (search; ZMODE, NOZ5, HUBONLY, THREADS), omega_profile.c (where far pairs are), omega_verify.py
(independent wiring check), hex_aut.py (Singer-type automorphisms of H(q) from moore_build coordinates), ubound.py /
ub_all.py (union bound), labs/ (the two q = 3 labellings).
