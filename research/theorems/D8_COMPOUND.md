# Diameter 8 from copies of the split Cayley hexagon: what a compound can and cannot do

Job own-d8-compound (Opus, 26 October 2026), branch `claude/own-d8-compound-1z4e6s`. Draft; sections marked
*(to be completed)* are filled in as the job runs.

Labels: **Theorem** (proved here, by hand), **Computer-checked** (a statement about specific graphs, with the check
named), **Heuristic** (an argument with a gap that is named).

Notation follows research/theorems/D7_HEXAGON.md (branch claude/d7-hexagon-theorems-4w1prt): $H = H(q)$ the split Cayley
hexagon, $P$, $L$ its points and lines, $N = |P| = |L| = (q^6-1)/(q-1)$, $I$ the incidence graph (bipartite,
$(q+1)$-regular, diameter 6, girth 12), $d$ the distance in $I$, $\Gamma_i(x)$ the elements at distance $i$ from $x$.
(F2): a unique geodesic joins $x, y$ when $d(x,y)\le 5$; when $d(x,y) = 6$ there is exactly one geodesic through each
neighbour of $x$. Point–line distances are $1, 3, 5$; same-type distances $0,2,4,6$.

## 0. The target

The 2013 table has, at diameter 8 and $\Delta = q+3$,
$$n_b(q+3, 8) \ge m(q)\cdot 2N(q),\qquad m(q) = 5\lfloor (q+5)/2\rfloor,$$
for $q = 7, 8, 9, 11, 13$ (cells (10,8), (11,8), (12,8), (14,8), (16,8); research/theorems/table_factor_out.txt on
branch claude/theorem-search-regularities-nt0d98). The source [DGQ] (Delorme–Gómez–Quisquater, "On large bipartite
graphs", cited on CombinatoricsWiki as submitted) was not found. This note asks which compounds of $m$ copies of $I$
with two extra edges per vertex can have diameter 8, proves what the simple mechanisms give, and records the evidence
about what [DGQ] must have used.

## 1. Reformulation

**Lemma 1.1 (Theorem).** A connected bipartite graph has diameter $\le 8$ iff every vertex is at distance $\le 7$ from
every vertex of the other colour class.

*Proof.* Distances between the classes are odd, so "$\le 8$" means "$\le 7$" there. If all cross distances are
$\le 7$ and $a, a'$ have the same colour, take a neighbour $b$ of $a'$: $d(a,a')\le d(a,b)+1\le 8$. $\square$

## 2. Lifts of $I$ plus two matchings

Let $\sigma_1,\sigma_2: P\to L$ be bijections and $B = I + \{p\sigma_t(p)\}$ (degree $q+3$). A *voltage assignment* in
a group $G$ gives a value to every dart; the lift $B^\alpha$ has vertices $(v,g)$ and edges $(u,g)\sim(v,g\alpha(u\to v))$.
It is bipartite of degree $q+3$ and order $|G|\cdot 2N$, and $G$ acts on it by left multiplication, so by Lemma 1.1
$B^\alpha$ has diameter $\le 8$ iff for every point $p$ and every line $y$ the voltages of the walks of length $\le 7$
from $p$ to $y$ cover $G$ (and the same from every line to every point, which is the same condition read backwards).

A walk is described by its *jumps* (matching edges, $U_t$: $p\to\sigma_t(p)$, $D_t$: $\sigma_t(p)\to p$) and its
hexagon segments. Call a walk family *guaranteed* if it exists for every $p$, $y$ and every choice of the bijections.
Since point–line distances in $I$ are $\le 5$ and same-type distances $\le 6$, the guaranteed families of length
$\le 7$ from a point $p$ to a line $y$ are (research/squads/cells/d10D8.md §3b on branch claude/bipartite-10-8-cell-um2c1t,
re-derived here):

| family | walk | count |
|---|---|---|
| $H$ | $p\leadsto y$ | 1 |
| $U_tH$ | $p\to\sigma_t(p)\leadsto y$ | 1, or $q+1$ if $y$ is opposite $\sigma_t(p)$ |
| $HU_t$ | $p\leadsto\sigma_t^{-1}(y)\to y$ | 1, or $q+1$ if $p$ is opposite $\sigma_t^{-1}(y)$ |
| $hD_tH$ | $p\to l\to\sigma_t^{-1}(l)\leadsto y$, $l\ni p$ | $q+1$ |
| $HD_th$ | $p\leadsto\sigma_t(x)\to x\to y$, $x\in y$ | $q+1$ |
| $U_sHU_t$ | $p\to\sigma_s(p)\leadsto\sigma_t^{-1}(y)\to y$ | 4 |
| $U_sD_tH$ ($s\ne t$) | $p\to\sigma_s(p)\to\sigma_t^{-1}\sigma_s(p)\leadsto y$ | 2 |
| $HD_sU_t$ ($s\ne t$) | $p\leadsto\sigma_s\sigma_t^{-1}(y)\to\sigma_t^{-1}(y)\to y$ | 2 |

(Every hexagon segment $\leadsto$ joins two arbitrary elements and has length $\le 5$ between types, $\le 6$ within a
type; every family has length $\le 7$.) In the worst case there are $4q+17$ guaranteed walks per pair.

### 2.1 Constant shifts: ten copies and no more from guaranteed walks

**Theorem 2.1** (the "ten levels" lemma of d10D8.md §2). Let all hexagon voltages be $0$ and give every edge of
matching $t$ the voltage $a_t\in\mathbb Z_m$. The guaranteed walks reach exactly the offsets
$$S(a_1,a_2) = \{0\}\cup\{\pm a_1,\pm a_2\}\cup\{a_s+a_t\}_{s,t}\cup\{a_1-a_2, a_2-a_1\}.$$
If $S = \mathbb Z_m$ the lift has diameter $\le 8$ for every choice of $\sigma_1,\sigma_2$. $|S|\le 10$, and
$S(1,4) = \mathbb Z_{10}$.

*Proof.* With zero hexagon voltages a walk's voltage is the signed sum of its jumps: $H$ gives $0$; $U_tH$, $HU_t$
give $a_t$; $hD_tH$, $HD_th$ give $-a_t$; $U_sHU_t$ gives $a_s+a_t$; $U_sD_tH$ and $HD_sU_t$ give $\pm(a_1-a_2)$. These
families exist for all $p, y$ (table above), so every offset in $S$ is reached from every point to every line; by
Lemma 1.1 and the $\mathbb Z_m$-symmetry this is diameter $\le 8$. Counting: $1 + 4 + 3 + 2 = 10$. For $a = (1,4)$:
$\{0,1,4,9,6,2,5,8,3,7\}$. $\square$

**Computer-checked 2.2.** `glift` (research/squads/cells/d10D8_work/glift.c, all sources) gives COST 0 for random
$\sigma_1,\sigma_2$ with shifts $(1,4)$ in $\mathbb Z_{10}$ at $q=3$ and $q=5$. With the same random matchings and
$m = 11$ the cost is 212 (shifts 1, 3) and 214 (1, 4) uncovered (source, target, copy) triples at $q=5$; with $m = 12$,
8,722 (1, 5) to 12,993,028 (1, 2). So walks that depend on the geometry of $\sigma_t$ (not guaranteed) already
cover almost everything one step beyond the lemma, but random matchings stop near $m = 11$.

### 2.2 Point-dependent shifts (coboundary voltages): about $2q$ copies at best *(to be completed)*

### 2.3 One matching and pencil-rainbow colourings *(to be completed: squad card c9)*

## 3. What [DGQ] must use *(to be completed)*

## 4. Squad rounds *(to be completed)*
