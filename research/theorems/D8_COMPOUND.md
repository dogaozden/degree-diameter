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

### 2.2 Point-dependent shifts: about $2q + O(\sqrt q)$ copies from guaranteed walks

Let the hexagon voltages be a coboundary (after relabelling the copies over each vertex they are $0$) and let the edge
$p\,\sigma_t(p)$ carry a voltage $e_t(p)$ that depends on the point. Write $\hat e_t(l) = e_t(\sigma_t^{-1}(l))$ for the
voltage of the matching edge at the line $l$. The guaranteed walks from $p$ to $y$ then have the voltages
$$A(p) = \{0, e_1(p), e_2(p)\}\cup\{-\hat e_t(l): l\ni p\}\cup\{e_s(p)-\hat e_t(\sigma_s(p))\}_{s\ne t},$$
$$B(y) = \{\hat e_1(y),\hat e_2(y)\}\cup\{-e_t(x): x\in y\}\cup\{e_t(z)-e_s(z) : z = \sigma_t^{-1}(y)\}_{s\ne t},\qquad
C(p,y) = \{e_s(p)+\hat e_t(y)\}_{s,t},$$
($H$, $U_tH$, $hD_tH$, $U_sD_tH$ depend on $p$ only; $HU_t$, $HD_th$, $HD_sU_t$ on $y$ only; $U_sHU_t$ on both).

**Theorem 2.3.** If $A(p)\cup B(y)\cup C(p,y) = \mathbb Z_m$ for every point $p$ and line $y$, then
$$m\ \le\ 2q + 11 + 2\sqrt{2q+9}.$$

*Proof.* For $g\ne 0$ let $x_g$ be the fraction of points $p$ with $g\in A(p)$ and $y_g$ the fraction of lines $y$ with
$g\in B(y)$; let $n_t(h) = |\{z\in P: e_t(z) = h\}|$, $\nu_g = \sum_t n_t(-g)/N$, $\mu_g = \sum_t n_t(g)/N$, and
$s^A_g$, $s^B_g$ the fractions of points (lines) whose two shadow values ($U_sD_tH$, resp. $HD_sU_t$) include $g$.
- $g = e_t(p)$ for a fraction $\le\mu_g$ of the points; $g = -\hat e_t(l)$ with $l\ni p$ only if $p$ lies on one of
  the $n_t(-g)$ lines $l$ with $\hat e_t(l) = -g$ ($\sigma_t$ is a bijection), which cover at most $(q+1)n_t(-g)$
  points. So $x_g\le z_g := (q+1)\nu_g + \mu_g + s^A_g + s^B_g$. The same count on the line side (a line contains a
  point $x$ with $e_t(x) = -g$ only if it is one of the $\le (q+1)n_t(-g)$ lines through such points) gives
  $y_g\le z_g$.
- Every pair $(p,y)$ with $g\notin A(p)$, $g\notin B(y)$ needs $g\in C(p,y)$, and $|C(p,y)|\le 4$, so
  $\sum_{g\ne0}(1-x_g)(1-y_g)\le 4$, hence $\sum_{g\ne 0}(1-\min(1,z_g))^2\le 4$.
- $\sum_g\nu_g = \sum_g\mu_g = 2$ and $\sum_g s^A_g, \sum_g s^B_g\le 2$, so $\sum_{g\ne0} z_g\le 2(q+1)+2+4 = 2q+8$.
With $n = m-1$ values and $w_g = \min(1,z_g)$: $\sum w_g\le 2q+8$ and $\sum(1-w_g)^2\le 4$; by convexity
$n(1-(2q+8)/n)^2\le 4$, i.e. $(n-2q-8)^2\le 4n$, so $n\le 2q+10+2\sqrt{2q+9}$. $\square$

So a construction "of Theorem-A type" (valid for every choice of the bijections, with trivial hexagon voltages) has at
most $2q + 11 + 2\sqrt{2q+9}$ copies: 34.6 at $q = 7$, 38.4 at $q = 9$, 43.1 at $q = 11$, 47.8 at $q = 13$. These
are above the table's 30, 35, 40, 45, so Theorem 2.3 does **not** decide whether [DGQ] needs hexagon voltages at
these $q$; but $5(q+5)/2$ exceeds the bound for every $q\ge 31$, so a uniform construction with that count must use
non-trivial hexagon voltages or walks that depend on the geometry of the matchings. The extremal case of the
inequality is not realistic: it needs about 30 values each covered from both sides for about 65% of the points and
lines, with the four mixed walks $U_sHU_t$ covering exactly the remaining pairs; nothing we built comes near it.
The heuristic version with "robust" values only (every value covered from one side for almost all points or lines)
gives $m\le 2q+O(1)$, which is where every untwisted design of the squads stopped.

### 2.3 One matching: pencil-rainbow colourings give $q+3$ copies

**Theorem 2.4.** Let $j = 1$ (one bijection $\sigma$, $\Delta = q+2$), $m = q+3$, hexagon voltages $0$. Suppose the lines
of $H(q)$ are coloured by $\mathbb Z_m\setminus\{0\}$ so that concurrent lines get different colours, let $\mu(p)$ be
the colour missing at the point $p$, and suppose $\sigma$ maps the points with $\mu(p) = a$ onto the lines of colour
$-a$, with voltage $e(p) = \mu(p)$. Then the lift has diameter $\le 8$.

*Proof.* From $(p,0)$: the line $y$ in copy $0$ by $H$; in copy $\mu(p)$ by $p\to\sigma(p)\leadsto y$ (length
$\le 1+6$); in the copy given by the colour of $l$, for each line $l\ni p$, by
$p\to l\to\sigma^{-1}(l)\leadsto y$ (length $\le 1+1+5$; the voltage is $-e(\sigma^{-1}(l)) = -\mu(\sigma^{-1}(l))$, which
is the colour of $l$ because $\sigma$ maps $\mu$-class $a$ onto colour class $-a$). The $q+1$ lines through $p$ carry all
colours except $\mu(p)$. So every copy is reached; Lemma 1.1. $\square$

Such a colouring has all colour classes of size $N/(q+2)$ (count incidences), so it needs $(q+2)\mid N(q)$; as
$N(q)\equiv -21 \pmod{q+2}$ this means $q\in\{5, 19\}$. At $q = 5$ (7 colours, classes of 558 lines) it would give
8 copies at $\Delta = 7$, where one random matching fails already at 5 copies; squad card c9 did not find the colouring
by tabu search (best 1,374 conflicting concurrent pairs), and existence is open. (The line-concurrence graph of $H(5)$
has eigenvalues $30, 9, -1, -6$; the Hoffman bound $651\ge 558$ does not exclude it.)

## 3. What [DGQ] must use (evidence, Heuristic)

- **Counts.** $m(q) = 5\lfloor(q+5)/2\rfloor$: $5 = 2j+1$ levels for $j = 2$ extra edges, as in the $D = 7$ level graph
  (Theorem A of D7_HEXAGON.md), and $\lfloor (q+5)/2\rfloor = 2 + \lfloor (q+1)/2\rfloor$ "sheets" per level, where
  $\lfloor(q+1)/2\rfloor$ is the number of disjoint pairs among the $q+1$ neighbours of a vertex (one left over for even
  $q$). The one-matching cell (13,8) = $15\cdot|I(H(11))|$ ($j = 1$) has $3\cdot 5$, i.e. $(q-1)/2$ sheets per level.
- **Levels with constant shifts cannot be the mechanism.** In the $\mathbb Z_5$ skeleton (shifts $+1$, $+2$) the
  only guaranteed walk to the own level is $H$, and the families with $q+1$ walks ($hD_tH$, $HD_th$) sit at levels
  $-1, -2$ (§2 table). With any two constant level shifts, at most four levels carry the large families. So the level
  of a walk must depend on more than its jumps: hexagon voltages, or point-dependent level shifts.
- **Random designs stop near $m \approx 12$** (q = 5, 7, 11; d14D8.md), annealing near 17 (q = 7, 11), and every
  structured family of round r1_d8c below the free 10 or the random value (§5).
- **Twisting is necessary for large $q$** (Theorem 2.3), and probably at $q = 7..13$ too: the only families that beat
  $2q + O(1)$ here use either a twisted hexagon or matchings with geometry (the duality of §4).

## 4. A duality as the matchings: pencil coordinates *(new, partly proved)*

For $q = 3^e$ the hexagon $H(q)$ has a duality $\delta$ (an incidence-preserving bijection $P\cup L\to L\cup P$
swapping types; [VM98]; computed for $q = 3, 9$ by research/d10D7/dual/dualfind.c and checked: all $N(q+1)$ flags are
preserved). Use it as both matchings: $B = I + \{p\,\delta(p)\}\times 2$ (two parallel edges per point), hexagon
voltages $0$, voltages $\beta_1(p),\beta_2(p)\in\mathbb Z_m$ on the two edges at $p$.

**Proposition 4.1 (Theorem: one-jump walks are intervals).** Let $p$ be a point and $y$ a line, $w = \delta^{-1}(y)$
(a point) and $\ell = \delta^{-1}(p)$ (a line). There is a walk of length $\le 7$ from $(p,0)$ to $(y,g)$ with exactly one
jump in each of the following cases:
- (+) $g = \beta_t(u)$ for a point $u$ with $d(p,u)+d(u,w)\le 6$ (walk $p\leadsto u\to\delta(u)\leadsto y$);
- (−) $g = -\beta_t(z)$ for a point $z$ with $d(\ell,z)+d(z,y)\le 6$ (walk $p\leadsto\delta(z)\to z\leadsto y$).

*Proof.* $\delta$ and $\delta^{-1}$ preserve distances in $I$: $d(\delta(u),y) = d(u,\delta^{-1}(y))$ and
$d(p,\delta(z)) = d(\delta^{-1}(p), z)$. The walk lengths are $d(p,u)+1+d(\delta(u),y)$ and $d(p,\delta(z))+1+d(z,y)$.
The lift edge $(u,h)\sim(\delta(u),h+\beta_t(u))$ gives the offsets. $\square$

**Proposition 4.2 (Theorem: the intervals).** (a) If $p, w$ are opposite points, the points $u$ with
$d(p,u)+d(u,w)\le 6$ are $p$, $w$ and the points of the two projective lines $m_1 = \pi_p\cap w^\perp$ and
$m_2 = \pi_w\cap p^\perp$ (each a line of PG(6,q) inside the totally singular plane $\pi_p$, resp. $\pi_w$, not through
$p$, resp. $w$; not a line of $H$). (b) If $\ell, y$ are opposite lines, the points $z$ with $d(\ell,z)+d(z,y)\le 6$
include all points of $\ell$ and all points of $y$ (lines of $H$). (c) If $d(p,w) = 4$, with geodesic
$p\,L\,u\,M\,w$, the points of (a) are exactly the points of the hexagon lines $L$ and $M$.

*Proof.* (a) A point $u\ne p,w$ with $d(p,u)+d(u,w) = 6$ lies on a geodesic, at distance 2 or 4 from $p$. The points at
distance 2 on the $q+1$ geodesics are the points $u_L\in L$ ($L\ni p$) with $d(u_L,w) = 4$, i.e. $u_L = L\cap w^\perp$
by (F4) ($L\not\subset w^\perp$ as $p\notin w^\perp$). They lie in $\pi_p\cap w^\perp$, which is a projective line not
through $p$ (as $\pi_p\not\subset w^\perp$); it has $q+1$ points and meets every line $L\ni p$ once, so it is exactly
$\{u_L\}$. Symmetrically for distance 4 (distance 2 from $w$). (b) For $z\in\ell$, $d(\ell,z) = 1$ and $d(z,y)\le 5$
(point–line); for $z\in y$, $d(z,y) = 1$ and $d(\ell,z)\le 5$. (c) is the same computation as (a) along the unique
geodesic: a point of $L$ other than $u$ has distances $2$ and $4$, a point collinear with $p$ off $L$ has distance
$6$ to $w$ (no shorter path without a cycle of length $<12$). $\square$

**Pencil coordinates.** Fix $a, a'\in\mathbb F_q^7$ and put $c(u) = [b(a,u):b(a',u)]\in PG(1,q)$; it is undefined on
the axis $\Pi = a^\perp\cap a'^\perp$ (a 5-dimensional subspace). On a projective line $m$ with $m\cap\Pi = \emptyset$
the map $u\mapsto c(u)$ is a bijection $m\to PG(1,q)$ (a linear map of the 2-space $m$ to $\mathbb F_q^2$ with trivial
kernel). Take $\beta_t = f_t\circ c$ with injective $f_t: PG(1,q)\to\mathbb Z_m$, images $B_1, B_2$.

**Corollary 4.3 (Theorem).** (Strong blocks.) For every point $p$ and line $y$, every offset of $-B_1\cup -B_2$ is
reached unless both hexagon lines $\delta^{-1}(p)$ and $y$ meet $\Pi$ (Proposition 4.2(b) holds for all $\ell, y$;
these walks are the guaranteed families $hD_tH$ and $HD_th$, with the colourings induced by $\delta$ and $c$). (Weak
blocks.) If $p$ and $w = \delta^{-1}(y)$ are opposite, every offset of $B_1\cup B_2$ is reached unless both ideal lines
$m_1, m_2$ meet $\Pi$. In particular, with symmetric blocks $B_t = -B_t$ and $m = 2q+3$ (so $\{0\}\cup B_1\cup B_2 =
\mathbb Z_m$; $q$ odd), the lift reaches every (point, line, copy) triple except possibly for pairs with both
$\delta^{-1}(p)$ and $y$ meeting the axis. With disjoint $\pm B_1, \pm B_2$ the count goes up to $4q+5$, at the price of
the weak-block exceptions.

**Obstruction 4.4 (Theorem).** Every totally singular plane $\pi_p$ meets $\Pi$ (a 3-dimensional subspace and the kernel
of a linear map onto $\mathbb F_q^2$). Hence $m_1 = \pi_p\cap w^\perp$ meets $\Pi$ whenever $w\perp u_0$ for a point
$u_0\in\pi_p\cap\Pi$, i.e. for about $1/q$ of the targets $w$, and the weak blocks fail for about $1/q^2$ of the
pairs. If $\pi_p\cap\Pi$ is a line, $m_1$ meets $\Pi$ for every $w$. Hexagon lines meet $\Pi$ only through the
$\approx q^3$ points of $H(q)$ on $\Pi$ (about $1/q$ of the lines).

**Computer-checked 4.5** (research/squads/cells/d10D8_work/pencil_dual.py + glift; diagnostics in this job's log).
- $q = 3$, $m = 17 = 4q+5$: for every third point and every line, the predicted offsets of Proposition 4.1 are a subset
  of the exact reach (no violation in 18,928 pairs); 1,440 pairs have an incomplete prediction, but only 70 pairs are
  really incomplete, all in the classes $(d(p,w), d(\ell,y)) = (6,6)$ and $(4,4)$. All-source cost 1,776.
- $q = 3$, robust core $m = 2q+3 = 9$ ($B_1 = [1,4]$, $B_2 = [5,8] = -B_1$): all-source COST 0 for axis seeds 1 and 4,
  COST 12 and 4 for seeds 2 and 3 (pairs where both relevant hexagon lines meet the axis); $m = 11$: 108, $m = 13$: 396.
- $q = 9$ (the (12,8) cell), 64 sampled sources: $m = 21$: cost 132 (6 bad sources); $m = 24$: 23,859; $m = 31$:
  81,062; $m = 36$: 166,260; $m = 41$: 381,875. At $m = 41$ all misses are in the weak blocks.
So the family is "almost" a design with $4q+5$ copies; what fails is exactly Obstruction 4.4. *(Round r2_d8c results:
§5.)*

## 5. Squad rounds

Round r1_d8c (16 cards): research/squads/LOG.md and research/squads/r1_d8c/. Round r2_d8c (6 cards, on §4):
*(to be completed)*.
