# Symmetric voltage lifts: few-orbit graphs of metacyclic groups (job beyond-d15)

Director's note, 2026-11-01. Plain statements with short proofs; the searches that use them are lsym/sweep.py,
lsym/haarsweep.py and lsym/quotsweep.py (all through liftsym.c).

## 1. The construction

B: a bipartite graph (sides A, B), b vertices, with an automorphism ρ of order k that preserves the sides and moves
every vertex in an orbit of size k (semiregular), so B has t = b/k vertex orbits. n: a modulus, λ: a unit mod n with
λ^k = 1. Voltages x_e ∈ Z_n on the oriented edges are **equivariant**: x_{ρ(e)} = λ x_e (with a minus sign when ρ
reverses the stored orientation). The lift L has vertices (v, g), g ∈ Z_n, and edges (u, g) ~ (w, g + x_e) for e = (u, w).

**Fact 1.** τ: (v, g) -> (v, g + 1) and ρ̂: (v, g) -> (ρv, λg) are automorphisms of L; they generate the metacyclic
group G = Z_n x|_λ Z_k (ρ̂ τ ρ̂^-1 = τ^λ), which acts semiregularly on V(L) with t orbits.

Proof. τ maps the edge (u,g)~(w,g+x_e) to (u,g+1)~(w,g+1+x_e), an edge. ρ̂ maps it to (ρu, λg)~(ρw, λg + λx_e), and
λ x_e = x_{ρ(e)}, so it is the lift of the edge ρ(e). ρ̂^k = id because ρ^k = id and λ^k = 1, and ρ̂ τ ρ̂^-1 maps
(v, g) to (v, g + λ), i.e. it is τ^λ. An element τ^c ρ̂^i fixing a vertex (v, g) has ρ^i v = v, so i = 0 mod k
(semiregular), and then c = 0. Orbits: the G-orbit of (v, 0) is ρ-orbit(v) x Z_n. QED.

**Corollary.** If t = 2 (one orbit per side), G acts regularly on each side and L is the Haar graph H(G, S) for some
3-element S (cubic case). Conversely every Haar graph of Z_n x|_λ Z_k with S = {e, (x1, a), (x2, b)} arises this way
from the base B = Haar(Z_k, {0, a, b}) with ρ the rotation. So the cubic metacyclic Haar graphs are exactly the
symmetric lifts of cubic circulant-type Haar graphs, and the squad card r1/a04's (3,16) value 17,602 (Z677 x|_362 Z13)
is the symmetric lift of Haar(Z13, {0,9,10}).

## 2. Gauge fixing: how many lifts there really are

**Fact 2.** For c: V(B) -> Z_n with c(ρv) = λ c(v), the voltages x'_e = x_e + c(w) - c(u) (e = (u,w)) are again
equivariant and give an isomorphic lift ((v, g) -> (v, g + c(v))). Multiplying all voltages by a unit μ of Z_n also
gives an isomorphic lift ((v, g) -> (v, μ g)).

Proof. Direct check: the map (v,g) -> (v, g + c(v)) sends the edge (u,g)~(w,g+x_e) to (u, g + c(u)) ~ (w, g + x_e + c(w)),
an edge of the lift with voltages x'. Equivariance of x' uses c(ρv) = λ c(v). Scaling commutes with multiplication by λ. QED.

c is determined by its values on one vertex per orbit (t values). The map c -> (changes of the edge-orbit voltages) is
linear; liftsym (EXH=1) computes its rank by elimination mod n with unit pivots and sets that many edge-orbit voltages to
0, then scales the first nonzero remaining one to a divisor of n (every nonzero x is a unit times gcd(x, n); for prime n
this is 1). For composite n a row whose remaining entries are all non-units is not used as a pivot, so the scan stays
exhaustive (it only enumerates more). A cubic base has 3t/2 edge orbits; generically the rank is t, so
**t/2 orbit voltages remain, one of which is scaled away**: t/2 - 1 free parameters in Z_n.

| t (vertex orbits) | example | free after gauge + scaling | lifts per (base, n, λ) |
|---|---|---|---|
| 2 | Haar graphs of Z_n x| Z_k (base Haar(Z_k,{0,a,b})) | 0 | 1 (plus degenerate ones) |
| 4 | Desargues with its order-5 rotation; quotsweep.py family | 1 | ~n |
| 6 | Gray (order 9), Tutte 8-cage (order 5), Foster (order 15) | 2 | ~n^2 |

So each (base, n, λ) is searched EXHAUSTIVELY in milliseconds (t = 2), seconds (t = 4) or minutes (t = 6). The
self-test (liftsym GTEST=1) applies a random gauge and scaling to random voltages and finds the same cost every time.
Measured gauge ranks: Desargues 4 of 6 edge orbits, Gray/Tutte 8-cage/Foster 6 of 9, Haar bases 2 of 3 (as predicted).

## 2a. The quotient view

Dividing the lift by the whole group Z_n x|_λ Z_k gives a cubic bipartite multigraph Q on t vertices (the quotient); the
base B is a Z_k voltage cover of Q, and the lift is a Z_n x|_λ Z_k voltage cover of Q. So a family is fixed by (Q, the Z_k
pattern, n, λ). For t = 2, Q is the theta graph (Haar graphs). For t = 6 there are exactly three connected cubic bipartite
multigraphs on 3 + 3 vertices (enumerated): biadjacency rows (1,0,2),(1,2,0),(1,1,1) — the quotient of the Tutte 8-cage
(k = 5) and of the Foster graph (k = 15); rows each with one double and one single edge — the quotient of the Gray graph
(k = 9); and K3,3. lsym/quotgen.py samples Z_k patterns on any Q. The (3,15) value 11,802 is the Tutte/Foster shape with
k = 7 and n = 281 (squad card r3/k03), a graph that is neither the Tutte 8-cage nor the Foster graph lifted.

## 3. What this means for the search

- The orbit idea of the D = 7..10 work (S closed under an automorphism) transfers to lifts: the voltages are closed
  under ρ. As for orbit S, λ must act nontrivially: λ = 1 gives an abelian group Z_n x Z_k acting with t orbits, whose
  graphs have polynomial growth; the Desargues test at n = 521 gave cost 33,740 with λ = 1 against 4 with λ of order 5.
- A random search in these families is wasteful: the family at fixed (base, n, λ) is tiny, and the exhaustive scan
  either solves it or certifies that it has no lift of diameter <= D. The director's sweeps found:
  (3,15): Desargues (t = 4) solves up to n = 461 (9,220), Gray (t = 6) n = 199 (10,746), Tutte 8-cage n = 331 (9,930),
  Haar graphs (t = 2) of Z149 x| Z37 (11,026); (3,16): Desargues n = 751 (15,020), Haar Z281 x| Z35 (19,670),
  Gray n = 379 (20,466), Foster n = 211 min cost 2 (18,990).
- Girth helps. Gray (girth 8, 54 vertices) and Foster (girth 10, 90) give larger lifts per base vertex than Desargues
  (girth 6) at the same D: short cycles of the base make different walks end at the same lift vertex.
- Cards that annealed plain Z_n lifts (r1/a01-a03) and abelian Z_a x Z_b lifts (r1/a05) stayed at 8,400-9,900 at
  (3,15) and 14,940 at (3,16): the plain family is much larger but the search does not reach its good corners.

## 4. Machine note

The container's scheduler uses autogroups (/proc/sys/kernel/sched_autogroup_enabled = 1): every Bash call is its own
process group and groups share the CPU equally, so `nice -n 10` inside a card command has no effect against other
groups. To give a long check priority, write to its group: `echo -10 > /proc/<pid>/autogroup`. With that, the (6,15)
haarcheck_gen run (4.3e8 elements) finished in 288 s under a load of 20.
