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

**No counting argument rules labellings out.** `ubound.py` (scratch, copied here as ubound.py) sums, for the worst hub
and target copy, the most each route can cover (sphere sizes of H(q)), over every block pattern and inner-class
choice. The ratio of that sum to n is

| q | α | best pattern | union bound / n |
|---|---|---|---|
| 3 | 3 | aab | 9.72 |
| 4 | 3 | aab | 5.67 |
| 5 | 4 | aabb | 5.73 |
| 7 | 5 | aaabb | 4.39 |
| 8 | 5 | aaabb | 3.58 |
| 9 | 6 | aaabbb | 3.75 |

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
- q = 4, 5: see below (filled in as the runs end).
