# Bipartite graphs of diameter 5 from generalized quadrangles: level graphs, surgery and hubs

Draft of 26 October 2026, written for Ignacio López and Gabriela Araujo-Pardo by the degree–diameter lab
(github.com/dogaozden/degree-diameter; Claude Code sessions coordinated by Doğa Özden). Job "thm-gq-d5".

This note does for diameter 5 and generalized quadrangles what research/theorems/D7_HEXAGON.md (branch
claude/d7-hexagon-theorems-4w1prt) does for diameter 7 and the split Cayley hexagon: $2r+1$ copies of the incidence graph
of a generalized quadrangle of order $(q,q)$, joined by perfect matchings, have diameter 5; deleting some matching edges
and attaching new "hub" vertices to the freed ends adds vertices. We state exactly which deletions survive, prove it,
and give the resulting families and one new record, $(13,5)$.

Every claim is labelled **Theorem** (with a complete proof here), **Computer-checked** (a computation, with the program
and its output in the repository), or **Heuristic** (an estimate, no proof). The neighbourhood of every vertex of every
graph is given explicitly (Definitions 2.1 and 3.1, and for the record the solution file of §11).

*File paths* refer to the repository github.com/dogaozden/degree-diameter, branch claude/gq-diameter-5-xa5d3d. The
tools are in research/theorems/d5gq/; the Haiku squad rounds that searched for sets and ran small-$q$ tests are in
research/squads/gqd5-r1/ and gqd5-r2/ (log: research/squads/LOG.md).

## Contents

0. Results
1. Generalized quadrangles: coordinates and facts
2. Level graphs
3. Surgery and hubs: the assembly theorem
4. Theorem E: the exact criterion for one transition
5. Theorem B: transitions that extend to an automorphism
6. Theorem C: local dualities, and why they stop at two points for $q$ odd
7. Relaxed freed sets of lines
8. Typed layouts and slot counts
9. Hub graphs
10. Families valid for every $q$
11. The $(13,5)$ record graph
12. Routing through a third level (computer experiments)
13. Quadrangles of order $(s,t)$ with $s\ne t$
14. Comparison with the 2013 table and the lab's values
15. Computer checks
16. Prior art

---

## 0. Results

Notation: $n_b(\Delta,D)$ is the largest order of a bipartite graph with maximum degree $\le\Delta$ and diameter $\le D$.
For a prime power $q$ put
$$N = N(q) = (q+1)(q^2+1),$$
the number of points (and of lines) of a generalized quadrangle of order $(q,q)$. The level graph of §2 with $2r+1$
levels has order $(2r+1)\cdot 2N(q)$ and degree $q+1+r$. In the 2013 table [MS13, Table 4] the cells $(10,5)$–$(15,5)$
have exactly this value for some $(q,r)$: $(10,5) = 5\cdot 2N(7)$, $(11,5) = 5\cdot 2N(8)$, $(12,5) = 5\cdot 2N(9)$,
$(13,5) = 7\cdot 2N(9)$, $(14,5) = 9\cdot 2N(9)$, $(15,5) = 7\cdot 2N(11)$ (the CombinatoricsWiki table credits them to
Delorme, Gómez and Quisquater; §16).

**New record.** $n_b(13,5)\ge 11{,}626$ (table 11,480; the lab's previous value 11,486). The graph: seven levels over
$Q(4,9)$ and its dual $W(9)$, an ovoid freed on five transitions, a computer-found set of 56 lines with 14 concurrent
pairs freed on five more, two-point local dualities on the other eleven, $86+60$ hubs (Corollary 11.1). It was checked by a
breadth-first search from every vertex (§15).

**Theorems.**

- **Theorem A** (§2; the construction is the table's): any typing, any bijections: diameter $\le 5$.
- **Theorem 3.5** (assembly): if every transition is *repaired* and same-colour hubs are within distance 4, then
  $n_b(q+1+r,5)\ge (2r+1)\cdot 2N + K_{\mathcal A}+K_{\mathcal B}$.
- **Theorem E** (§4): a transition with matching $M$ and freed set $R$ is repaired **if and only if** three covering
  conditions (E1)–(E3) hold. This is new compared with the $D=7$ note, where only sufficient conditions were given.
- **Theorem B** (§5): a transition whose matching extends to an automorphism (the identity between a quadrangle and its
  dual, or a duality) is repaired if and only if its freed set is a **partial ovoid** (resp. partial spread). The
  "segment sets" of the hexagon do not survive at $D=5$.
- **Theorem C** (§6): a local duality on a non-collinear freed set repairs a transition; at $D=5$ the condition on
  $M(R)$ is not needed. **Corollary 6.3**: for $q$ odd, a local duality between $Q(4,q)$ and itself (or $W(q)$ and
  itself) exists on at most **two** points, because point triads of $Q(4,q)$ have 0 or 2 centres and line triads 1 or
  $q+1$. **Proposition 6.4**: two points always work.
- **Proposition 7.2** (§7): freed lines may come in concurrent pairs if the hubs at their slots sit at the ovoid point
  of the partner line.
- **Families** (§10), valid for every $q$, with explicit sets and explicit hub graphs, e.g. for $q$ odd
  $n_b(q+4,5)\ge 14N(q)+K_{\mathcal A}+K_{\mathcal B}$ with $K_{\mathcal B}$, $K_{\mathcal A}$ given by
  explicit sets of sizes $\min(q^2+5,\,6q)$ and $3q+3$; these alone exceed the 2013 table in the cells
  $(10,5)$–$(15,5)$ (§14).

**What does not work** (§§12–14): the level-graph family stays below the lab's values (doubled-matching lifts and
route-chart lifts) in $(10,5)$, $(11,5)$, $(12,5)$, $(14,5)$, $(15,5)$, $(16,5)$, and far below at $\Delta\le 9$. At
$(15,5)$ the best graph of this kind we built has 20,696 vertices, 40 short of the lab's 20,736; §14 explains which
quantity limits it.

---

## 1. Generalized quadrangles

### 1.1 Definition and distances

A *generalized quadrangle* (GQ) of order $(s,t)$, $s,t\ge 1$, is an incidence structure $\mathcal S = (P, L,
\mathrm I)$ of points and lines in which every line has $s+1$ points, every point is on $t+1$ lines, two points are on
at most one common line, and

**(GQ)** for every point $p$ and line $\ell$ with $p\notin\ell$ there is exactly one point of $\ell$ collinear with $p$
(equivalently, exactly one line through $p$ meets $\ell$).

Then $|P| = (s+1)(st+1)$ and $|L| = (t+1)(st+1)$ [PT, 1.2.1]. The *dual* $\mathcal S^D$ (points and lines exchanged)
is a GQ of order $(t,s)$. A *duality* of $\mathcal S$ is an isomorphism $\mathcal S\to\mathcal S^D$.

$I = I(\mathcal S)$ is the incidence graph (vertex set $P\cup L$). $d(x,y)$ is the distance in $I$,
$\Gamma_i(x) = \{y: d(x,y) = i\}$. Points are at even distance from points; $\Gamma_2(p)$ is the set of the $s(t+1)$
points collinear with $p$, and $\Gamma_2(\ell)$ the set of the $t(s+1)$ lines meeting $\ell$. For a set $X$ of points,
$X^\perp$ is the set of points collinear with (or equal to) every point of $X$; $\{x,y\}^\perp$ for non-collinear
$x,y$ has $t+1$ points, and its points are the *centres* of a triad $\{x,y,z\}$ when they are also collinear with $z$.

We use:

**(F1)** $I$ is connected, bipartite, of diameter 4 and girth 8; points have degree $t+1$, lines $s+1$.
*Proof.* Two points are at distance 2 (collinear) or, by (GQ) applied to $p$ and any line through $p'$, at distance
4; a point and a line are at distance 1 or 3 by (GQ); two lines are at distance $\le 4$ dually. A cycle of length 4 would
be two points on two lines; a 6-cycle is a triangle, excluded by (GQ). $\square$

**(F2)** If $d(x,y)\le 3$ there is a unique geodesic from $x$ to $y$.

**(F3) Covering lemma.** For elements $x,y$ there is $z\in\Gamma_2(x)$ with $d(z,y)\le 1$ if $x,y$ have different
types and $d(z,y)\le 2$ if they have the same type. Moreover, if $x$ and $y$ have different types, some element of
$\Gamma_2(x)$ is incident with $y$.
*Proof.* If $d(x,y)\ge 2$ take $z$ at distance 2 from $x$ on a geodesic. If $d(x,y) = 1$ take
$z\in\Gamma_1(y)\smallsetminus\{x\}$ (it exists as $s,t\ge 1$); then $z\in\Gamma_2(x)$ and $z$ is incident with $y$. If
$x = y$ any $z\in\Gamma_2(x)$ has $d(z,y) = 2$. For different types $d(x,y)\in\{1,3\}$, and in both cases the $z$
found is incident with $y$. $\square$

**(F4)** A line $\ell$ not through $p$ contains exactly one point of $\Gamma_2(p)$; every line through $p$ contains
$s$ points of $\Gamma_2(p)$. In particular $\Gamma_2(p)$ meets every line. (This is (GQ).)

### 1.2 The classical quadrangles in coordinates

$q$ is a prime power. All our computations use the following coordinates (research/theorems/d5gq/gqlib.py).

**$W(q)$**, order $(q,q)$: the points of $\mathrm{PG}(3,q)$, and the lines of $\mathrm{PG}(3,q)$ that are totally
isotropic for the symplectic form
$$w(x,y) = x_0y_2 + x_1y_3 - x_2y_0 - x_3y_1 .$$
Two distinct points $x,y$ are collinear in $W(q)$ if and only if $w(x,y) = 0$. The $q+1$ lines through $x$ are the
lines through $x$ in the plane $x^{\perp_w}$.

**$Q(4,q)$**, order $(q,q)$: the points of the parabolic quadric
$$X_0X_1 + X_2^2 + X_3X_4 = 0\quad\text{in }\mathrm{PG}(4,q),$$
and the lines on it. We use it through the Klein correspondence: a line $\langle x,y\rangle$ of $\mathrm{PG}(3,q)$ has
Plücker coordinates $p_{ij} = x_iy_j-x_jy_i$ on the Klein quadric $p_{01}p_{23}-p_{02}p_{13}+p_{03}p_{12} = 0$; it is
totally isotropic for $w$ exactly when $p_{02}+p_{13} = 0$, and then
$(X_0,\dots,X_4) = (p_{01},p_{23},p_{02},p_{03},p_{12})$ is a point of the quadric above. This maps the lines of $W(q)$
bijectively onto the points of $Q(4,q)$, and the pencils of $W(q)$ onto the lines of $Q(4,q)$; so $Q(4,q)\cong W(q)^D$
[PT, 3.2.1]. In the programs $Q(4,q)$ is literally `W(q).dual()`: point $i$ of $Q(4,q)$ is line $i$ of $W(q)$ and line
$j$ of $Q(4,q)$ is point $j$ of $W(q)$.

**$Q(5,q)$**, order $(q,q^2)$: the elliptic quadric $X_0X_1+X_2X_3+f(X_4,X_5) = 0$ in $\mathrm{PG}(5,q)$, $f$ an
irreducible binary quadratic form; **$H(3,q^2)$** $= Q(5,q)^D$, order $(q^2,q)$. **$T_2(O)$** for an oval $O$ of
$\mathrm{PG}(2,q)$ (order $(q,q)$; for $q$ odd $O$ is a conic and $T_2(O)\cong Q(4,q)$). **$AS(q)$**, $q$ odd, order
$(q-1,q+1)$; we build it as the Payne derivative $P(W(q),x)$ at a point $x$ (points: the $q^3$ points not collinear
with $x$; lines: the lines of $W(q)$ not through $x$, restricted, and the hyperbolic lines $\{x,y\}^{\perp\perp}$ minus
$x$) [PT, 3.2.6]. Only $W(q)$ and $Q(4,q)$ enter the theorems of §§2–11; §13 explains why.

All generators were checked against the GQ axioms by computer for $q\le 5$ ($W$, $Q(4,q)$), $q\le 3$ ($Q(5,q)$,
$H(3,q^2)$) and $q = 3,5$ ($AS(q)$) (research/theorems/d5gq/gqlib.py, self-test).

### 1.3 Ovoids, spreads, triads

A *partial ovoid* is a set of pairwise non-collinear points (in a GQ "non-collinear" and "opposite" coincide, as the
diameter of $I$ is 4); an *ovoid* is a partial ovoid meeting every line, i.e. with $st+1$ points. Dually *partial
spread* and *spread*. In $W(q)$ and $Q(4,q)$ ovoids and spreads have $q^2+1$ elements.

**Lemma 1.1 (an explicit spread of $W(q)$, hence an explicit ovoid of $Q(4,q)$).** Choose $\alpha,\beta\in\mathbb F_q$
with $X^2-\beta X-\alpha$ irreducible. The $q^2+1$ lines
$$\ell_\infty = \langle e_2,e_3\rangle,\qquad \ell_{a,b} = \langle (1,0,a,b),\ (0,1,b,\alpha a+\beta b)\rangle\quad(a,b\in\mathbb F_q)$$
form a spread of $W(q)$, for every $q$.
*Proof.* $w$ vanishes on $\ell_\infty$, and $w((1,0,a,b),(0,1,b,c)) = b - b = 0$, so all are lines of $W(q)$. The
line $\ell_{a,b}$ is $\{(u,uA): u\in\mathbb F_q^2\}$ with $A = \begin{pmatrix} a&b\\ b&\alpha a+\beta b\end{pmatrix}$,
so $\ell_{a,b}\cap\ell_{a',b'}\neq\emptyset$ iff $A-A'$ is singular, i.e.
$\delta_a(\alpha\delta_a+\beta\delta_b) - \delta_b^2 = 0$ with $(\delta_a,\delta_b) = (a-a',b-b')$. If
$\delta_a\ne 0$, put $t = \delta_b/\delta_a$: this says $t^2-\beta t-\alpha = 0$, impossible; if $\delta_a = 0$ it says
$\delta_b = 0$. No $\ell_{a,b}$ meets $\ell_\infty$. So the $q^2+1$ lines are pairwise disjoint and cover all
$(q^2+1)(q+1)$ points. $\square$

Under the Klein correspondence these lines are $q^2+1$ pairwise non-collinear points of $Q(4,q)$: an ovoid $O$ of
$Q(4,q)$. (It is an elliptic quadric section, but we do not need that.)

**Lemma 1.2 (facts we cite).**
(a) $W(q)$ has a spread for every $q$ (Lemma 1.1); $W(q)$ has an ovoid iff $q$ is even; dually $Q(4,q)$ has an ovoid
for every $q$ and a spread iff $q$ is even [PT, 3.4.1, 3.4.2].
(b) $W(q)$ is self-dual iff $q$ is even [PT, 3.2.1]; for $q$ even $W(q)\cong Q(4,q)$.
(c) All points of $W(q)$ are regular; the points of $Q(4,q)$ are regular for $q$ even and antiregular for $q$ odd
[PT, 3.3.1]. In a GQ of order $(s,s)$, a point $x$ is regular iff every triad containing $x$ has 1 or $s+1$ centres,
and antiregular iff every such triad has 0 or 2 centres [PT, 1.3.6]. So for $q$ odd: **triads of points of $Q(4,q)$
have 0 or 2 centres; triads of lines of $Q(4,q)$ (= triads of points of $W(q)$) have 1 or $q+1$ centres.**
(d) (Tallini [Ta91]) A partial ovoid of $W(q)$, $q$ odd, has at most $q^2-q+1$ points. (Klein–Metsch [KM]: a partial
spread of $Q(4,q)$ with more than $q^2-q+1$ lines is contained in a spread; for $q$ odd there is none.)

*Computer-checked* (research/theorems/d5gq/triads.py, triads_out.txt): on 3,000 random triads each, $W(q)$ shows only
1 and $q+1$ centres and $Q(4,q)$ only 0 and 2, for $q = 3,5,7$.

**Lemma 1.3 (an explicit partial ovoid of $W(q)$ of size $3q-1$, $q$ odd, $q\ge 5$).** (Found by squad card r2c10;
research/squads/gqd5-r2/c10/.) Write points of $\mathrm{PG}(3,q)$ as $(u,v)$ with $u,v\in\mathbb F_q^2$, so that
$w((u,v),(u',v')) = u\cdot v' - v\cdot u'$ with the dot product $u\cdot v = u_0v_0+u_1v_1$. Put
$v^\perp = (-v_1,v_0)$ (so $u\cdot v^\perp = 0$ iff $u,v$ are proportional), $a_1 = (1,0)$, $a_2 = (0,1)$,
$a_3 = (1,1)$, $b_i = a_{i-1}^\perp$ (indices mod 3), and
$$S = \{(a_i, c\,b_i): i = 1,2,3,\ c\in\mathbb F_q^*\}\ \cup\ \{(x,0),\ (0,z^\perp)\}$$
with $x = (1,\tau)$, $\tau\notin\{0,1\}$, and $z\notin\{a_1,a_2,a_3,x\}$ (projectively). Then $S$ is a partial
ovoid of $W(q)$ with $3q-1$ points.
*Proof.* For $P = (a,cb)$, $P' = (a',c'b')$: $w(P,P') = c'(a\cdot b')-c(b\cdot a')$.
Same $i$, $c\ne c'$: $w = (c'-c)(a_i\cdot b_i)\ne 0$ since $a_i\ne a_{i-1}$.
Different $i,j$: $a_i\cdot b_j = 0$ iff $a_i = a_{j-1}$ iff $i = j-1$, and $b_i\cdot a_j = 0$ iff $j = i-1$; for
$i\ne j$ in $\mathbb Z_3$ exactly one of these holds, so $w$ is a non-zero element times a non-zero element: $w\ne 0$.
$(x,0)$ against $(a_i,cb_i)$: $w = c\,(x\cdot b_i)$, zero iff $x = a_{i-1}$, excluded. $(0,z^\perp)$ against
$(a_i,cb_i)$: $w = -z^\perp\cdot a_i$, zero iff $a_i = z$, excluded. $(x,0)$ against $(0,z^\perp)$: $w = x\cdot
z^\perp\ne 0$ as $z\ne x$. The points are distinct, $3(q-1)+2$ of them. $\square$

(For $q = 3$ the point $(0,z^\perp)$ is not available, and the three orbits with $(x,0)$, $x = (1,-1)$, give 7 points,
the maximum for $W(3)$; computer-checked for $q = 3,5,7,9,11,13$ with gqlib.) Computer searches find much larger
partial ovoids for specific $q$ (§10.3): 18 ($q=5$), 33 ($q=7$), 51 ($q=9$), 70 ($q=11$). We know no explicit family
of order $q^2$ for $q$ odd; the literature has $(q^{3/2}+3q-q^{1/2}+3)/3$ for $q$ an odd square, $3\nmid q$ [CDPS].

---

## 2. Level graphs

Let $\mathcal S$ be a GQ of order $(s,s)$, so $|P| = |L|$; $I$ its incidence graph. Fix $r\ge 1$ and a *regular
tournament* $T$ on the vertex set $\mathbb Z_{2r+1}$ ("levels"): every two levels are joined by exactly one arc, and
every level has $r$ outgoing arcs. The *rotational* tournament has the arcs $j\to j+k$, $1\le k\le r$. Each level gets
a type $\tau_j\in\{H,D\}$ with
$$A(H) = P,\quad B(H) = L,\qquad A(D) = L,\quad B(D) = P.$$
An arc $t = (j\to j')$ is a *transition*; it is *friendly* if $\tau_j\ne\tau_{j'}$ (then $A(\tau_j) = B(\tau_{j'})$).

**Definition 2.1 (level graph).** Given a bijection $M_t: A(\tau_j)\to B(\tau_{j'})$ for every arc $t = (j\to j')$,
$X = X(T,\tau,M)$ has vertex set $(P\cup L)\times\mathbb Z_{2r+1}$ and edges $(x,j)\sim(y,j)$ for incident $x,y$
("level edges") and $(a,j)\sim(M_t(a),j')$ for every arc $t = (j\to j')$ and $a\in A(\tau_j)$ ("matching edges").
Colour $(a,j)$, $a\in A(\tau_j)$, with $\mathcal A$ and $(b,j)$, $b\in B(\tau_j)$, with $\mathcal B$. Neighbourhoods:
$$N_X(a,j) = \Gamma_1(a)\times\{j\}\cup\{(M_t(a),j'): t = (j\to j')\in T\},\qquad
N_X(b,j') = \Gamma_1(b)\times\{j'\}\cup\{(M_t^{-1}(b),j): t = (j\to j')\in T\}.$$
$X$ is bipartite (colours $\mathcal A$, $\mathcal B$), $(s+1+r)$-regular, of order $(2r+1)\cdot 2|P|$.

With all types $H$, one bijection $\sigma:P\to L$ on every arc and $(s,s) = (q,q)$ this is the graph of the 2013 table
values listed in §0 (two plain matchings over $\mathbb Z_5$, three over $\mathbb Z_7$, four over $\mathbb Z_9$).

**Theorem A.** For every tournament, typing and choice of bijections, $X$ has diameter at most 5. Precisely: two
vertices of one level are joined inside the level by a path of length $\le 4$; for every arc $t = (j\to j')$, every
vertex of level $j$ is joined to every vertex of level $j'$ by a path of length $\le 5$ that uses only level edges of
levels $j,j'$ and matching edges of $t$.

*Proof.* Inside a level: (F1). Let $t = (j\to j')$, $M = M_t$, and take $(u,j)$, $(v,j')$. Elements of different types
are at distance $\le 3$ in $I$, of equal type at distance $\le 4$.
1. $u\in A(\tau_j)$: $(u,j)\to(M(u),j')\leadsto(v,j')$, length $\le 1+4$.
2. $u\in B(\tau_j)$, $v\in B(\tau_{j'})$: $(u,j)\leadsto(M^{-1}(v),j)\to(v,j')$, length $\le 3+1$.
3. $u\in B(\tau_j)$, $v\in A(\tau_{j'})$: take $b\in\Gamma_1(v)$: $(u,j)\leadsto(M^{-1}(b),j)\to(b,j')\to(v,j')$,
   length $\le 3+1+1$. $\square$

*Computer-checked*: research/theorems/d5gq/test_basic.py (output test_basic_out.txt) built 32 level graphs with random
types and random bijections over $W(q)$ and $Q(4,q)$, $q = 2,3,4,5$, $r = 1,2$; all have diameter exactly 5.

**Proposition 2.2 (unequal orders).** If $\mathcal S$ has order $(s,t)$ with $s\ne t$ and $2r+1\ge 3$, no typing of a
tournament on the levels makes every arc friendly, and a non-friendly arc needs a bijection between $P$ and $L$, which
do not have the same size. So Definition 2.1 with perfect matchings exists only for $s = t$.
*Proof.* Three levels span a triangle of the tournament, and two of them have the same type; the arc between them is
not friendly. $|P|-|L| = (s-t)(st+1)\ne 0$. $\square$

---

## 3. Surgery and hubs

**Definition 3.1.** Start from $X(T,\tau,M)$ and choose for every arc $t = (j\to j')$ a set
$R_t\subseteq A(\tau_j)$ of *freed elements*.
1. *Deletion.* Delete the matching edges $(a,j)(M_t(a),j')$, $a\in R_t$. Each leaves a free $\mathcal A$-slot $(a,t)$
   at $(a,j)$ and a free $\mathcal B$-slot $(M_t(a),t)$ at $(M_t(a),j')$. Level $j$ has
   $\alpha_j = \sum_{t\text{ out of }j}|R_t|$ free $\mathcal A$-slots and $\beta_j = \sum_{t\text{ into }j}|R_t|$ free
   $\mathcal B$-slots. Call the result $X_R$.
2. *Hubs.* Add $K_{\mathcal B}\le\min_j\alpha_j$ vertices of colour $\mathcal B$ ($\mathcal B$-hubs) and
   $K_{\mathcal A}\le\min_j\beta_j$ vertices of colour $\mathcal A$ ($\mathcal A$-hubs). Each $\mathcal B$-hub $h$
   takes one free $\mathcal A$-slot in every level, at the vertex $(\omega_j(h),j)$, and each $\mathcal A$-hub $g$ one
   free $\mathcal B$-slot in every level, at $(\omega'_j(g),j)$; every slot is taken at most once.
3. *Hub graph.* Add a bipartite graph $Y$ between the $\mathcal B$-hubs and the $\mathcal A$-hubs.

Call the result $X_R^+$. Neighbourhoods: a level vertex has the neighbourhood of Definition 2.1 minus its deleted
matching edges plus one hub per taken slot; a hub has
$N(h) = \{(\omega_j(h),j): j\}\cup N_Y(h)$ and $N(g) = \{(\omega'_j(g),j): j\}\cup N_Y(g)$. $X_R^+$ is bipartite
(hubs join the opposite colour), level vertices have degree $\le s+1+r$, hubs $2r+1+\deg_Y$; so the maximum degree
is $\le s+1+r$ as soon as $Y$ has maximum degree $\le s-r$. The order is $(2r+1)\cdot 2|P|+K_{\mathcal A}+K_{\mathcal B}$.

(A hub must have a neighbour in every level in our constructions; a vertex joined to an $\mathcal A$-vertex of one level
and a $\mathcal B$-vertex of another would break bipartiteness, as squad card c17 also found by experiment.)

**Lemma 3.2 (one matching edge).** Let $t = (j\to j')$. A path of length $\le 5$ from level $j$ to level $j'$ that uses
only level edges of $j,j'$ and remaining matching edges of $t$ uses exactly one matching edge.
*Proof.* It uses an odd number of them. With three or more, write the path as
$(u,j)\leadsto(a_1,j)\to(M(a_1),j')\leadsto(M(a_2),j')\to(a_2,j)\leadsto(a_3,j)\to\cdots$. A shortest such path does
not use the same edge twice, so $a_1\ne a_2$ and $a_2\ne a_3$; $M(a_1), M(a_2)$ have the same type, so they are at
distance $\ge 2$, and so are $a_2,a_3$. The length is then $\ge 3+2+2 = 7$. $\square$

**Definition 3.3.** The transition $t$ is *repaired* (by $R_t$) if in $X_R$ every vertex of level $j$ is joined to
every vertex of level $j'$ by a path of length $\le 5$ using only level edges of $j,j'$ and remaining matching edges of
$t$. By Lemma 3.2: iff for all $u,v$ there is $a\in A(\tau_j)\smallsetminus R_t$ with
$$d(u,a)+1+d(M_t(a),v)\ \le\ 5. \tag{3.1}$$

**Lemma 3.4 (hubs reach everything).** In $X_R^+$ every hub is within distance 5 of every level vertex, and every
$\mathcal B$-hub within distance 5 of every $\mathcal A$-hub.
*Proof.* $h\to(\omega_j(h),j)\leadsto(v,j)$ has length $\le 1+4$. For $h$, $g$: $\omega_0(h)\in A(\tau_0)$ and
$\omega'_0(g)\in B(\tau_0)$ have different types, so $h\to(\omega_0(h),0)\leadsto(\omega'_0(g),0)\to g$ has length
$\le 1+3+1$. $\square$

**Theorem 3.5 (assembly).** Suppose
- (T) every transition $t$ is repaired by $R_t$, and
- (HG) any two $\mathcal B$-hubs, and any two $\mathcal A$-hubs, are within distance 4 in $X_R^+$.

Then $X_R^+$ has diameter $\le 5$. If moreover $Y$ has maximum degree $\le q-r$ (order $(q,q)$), then
$$n_b(q+1+r,5)\ \ge\ (2r+1)\cdot 2N(q)+K_{\mathcal A}+K_{\mathcal B}.$$
*Proof.* Level pairs: (F1) inside a level, (T) between levels (every pair of levels is an arc). Pairs with a hub: Lemma
3.4 and (HG). Same-colour vertices are at even distance, so "within 5" means "within 4" for them. $\square$

(HG) holds if $Y$ alone has all same-colour distances $\le 4$ (§9); paths through the levels may also help.

---

## 4. Theorem E: the exact criterion

**Theorem E.** Let $t = (j\to j')$ be any transition of a level graph over a GQ of order $(s,s)$, $M = M_t$,
$R = R_t\subseteq A(\tau_j)$. Then $t$ is repaired if and only if
- **(E1)** it is not the case that some element of $B(\tau_j)$ has all its incident elements in $R$ *and* some element
  of $A(\tau_{j'})$ has all its incident elements in $M(R)$;
- **(E2)** for every $x\in R$, every element of $A(\tau_{j'})$ is incident with $M(a)$ for some
  $a\in\Gamma_2(x)\smallsetminus R$;
- **(E3)** for every $x\in R$, every element of $B(\tau_j)$ is incident with some $a\notin R$ such that
  $M(a)\in\Gamma_2(M(x))$.

*Proof.* We check (3.1) for all $(u,v)$, sorted by the colours of $u$ (in level $j$) and $v$ (in level $j'$). Recall:
$d(u,a)$ is even iff $u,a$ have the same type; $M(a)$ has the type of $B(\tau_{j'})$; elements of different types are at
distance $\le 3$.

(i) $u\in A(\tau_j)\smallsetminus R$: $a = u$ gives $0+1+d(M(u),v)\le 5$. Always fine.

(ii) $u = x\in R$, $v\in A(\tau_{j'})$: we need $a\ne x$ with $d(x,a)+d(M(a),v)\le 4$; $d(x,a)\ge 2$ is even and
$d(M(a),v)\ge 1$ is odd, so the only possibility is $d(x,a) = 2$, $d(M(a),v) = 1$. This holds for all $v$ iff (E2)
holds for $x$.

(iii) $u = x\in R$, $v\in B(\tau_{j'})$: if (E2) holds, pick $w\in\Gamma_1(v)$ (it is in $A(\tau_{j'})$) and
$a\in\Gamma_2(x)\smallsetminus R$ with $M(a)$ incident with $w$; then $d(x,a)+d(M(a),v)\le 2+2$. So (iii) follows from (E2).

(iv) $u\in B(\tau_j)$, $v\in A(\tau_{j'})$: both distances are odd, so the possibilities are $(1,1),(1,3),(3,1)$. If some
$b\in\Gamma_1(v)$ has $M^{-1}(b)\notin R$, take $a = M^{-1}(b)$: $d(u,a)\le 3$, total $\le 4$. If some
$a\in\Gamma_1(u)\smallsetminus R$ exists, $d(M(a),v)\le 3$ gives total $\le 4$. If neither ($\Gamma_1(v)\subseteq M(R)$ and
$\Gamma_1(u)\subseteq R$), every $a\notin R$ has $d(u,a)\ge 3$ and $d(M(a),v)\ge 3$: the pair fails. So (iv) holds for
all pairs iff (E1) holds.

(v) $u\in B(\tau_j)$, $v\in B(\tau_{j'})$: $d(u,a)$ odd, $d(M(a),v)$ even; total $\le 4$ means $(1,0),(1,2)$ or $(3,0)$.
If $v\notin M(R)$, $a = M^{-1}(v)$ works ($3+0$). If $v = M(x)$, $x\in R$: $d(M(a),v) = 0$ would force $a = x$, so we
need $a\in\Gamma_1(u)\smallsetminus R$ with $M(a)\in\Gamma_2(M(x))$; for all $u$ this is (E3) for $x$.

These cases cover all pairs ($u\in A\smallsetminus R$: (i); $u\in R$: (ii),(iii); $u\in B$: (iv),(v)). $\square$

*Computer-checked*: test_basic.py compares (E1)–(E3) (repair.py, `exact_conditions`) with a brute-force evaluation of
(3.1) over all pairs (repair.py, `brute_bad`): 30 random friendly and non-friendly transitions for each $q = 2,3,4,5$,
and 300 transitions with whole lines and pencils inside $R$ for $q = 2,3$ (every failure type occurs); they agree in
every case.

---

## 5. Theorem B: automorphic transitions

A transition is *automorphic* if $M_t$ is the restriction of an automorphism $\psi$ of $I$ with
$\psi(A(\tau_j)) = B(\tau_{j'})$: a friendly transition with $M_t = \mathrm{id}$, or a non-friendly one with $M_t$ a
duality (which exists for $W(q)$ iff $q$ is even, Lemma 1.2(b)).

**Theorem B.** An automorphic transition with $A(\tau_j) = P$ is repaired if and only if $R_t$ is a partial ovoid
(pairwise non-collinear). Dually, with $A(\tau_j) = L$, iff $R_t$ is a partial spread.

*Proof.* Take $A(\tau_j) = P$. (E2) for $x$: $\psi(a)$ is incident with $v$ iff $a$ is incident with $\psi^{-1}(v)$, and
$\psi^{-1}$ maps $A(\tau_{j'})$ onto $B(\tau_j) = L$. So (E2) for $x$ says: every line contains a point of
$\Gamma_2(x)\smallsetminus R$. By (F4), a line through $x$ contains $s\ge 1$ points of $\Gamma_2(x)$ and a line $\ell$ not
through $x$ exactly one, $p_\ell$. If $R\cap\Gamma_2(x) = \emptyset$ every line is covered. If $y\in R\cap\Gamma_2(x)$,
a line $\ell\ne xy$ through $y$ (it exists, $t\ge 1$) has $p_\ell = y\in R$ and is not covered. So (E2) for all
$x\in R$ $\iff$ $R$ is non-collinear. (E3) for $x$: $M(a)\in\Gamma_2(M(x))$ iff $a\in\Gamma_2(x)$, so (E3) is the same
statement. (E1): if $R$ is non-collinear no line has all its $s+1\ge 2$ points in $R$, so the first half of (E1)
fails and (E1) holds. $\square$

So at $D = 5$ the freed sets of automorphic transitions are exactly the partial ovoids; there is no analogue of the
hexagon's segment sets (a pair of collinear freed points already breaks the transition). For $W(q)$ and $Q(4,q)$ the
largest are the ovoids, $q^2+1$ points, when they exist (Lemma 1.2(a)).

*Computer-checked*: test_basic.py, 30 random sets per $q\le 5$ (half partial ovoids, half not): repaired iff partial
ovoid. Squad card c9 built a three-level graph over $Q(4,5)$ with an 18-line partial spread plus one concurrent line on
a friendly transition and no hubs: 72 ordered pairs at distance 6, as Theorem B predicts for the two levels.

---

## 6. Theorem C: local dualities

For a non-friendly transition between two levels over the same quadrangle (a map $M: P\to L$ of $W(q)$ or of
$Q(4,q)$) there is no duality when $q$ is odd. We ask $M$ to behave like one near $R$.

**Theorem C.** Let $t$ be any transition, $M = M_t$, $R = R_t$. If
- (H1) $R$ is non-collinear (resp. non-concurrent), and
- (H3) $M(\Gamma_2(x)) = \Gamma_2(M(x))$ for every $x\in R$,

then $t$ is repaired.

*Proof.* (E2) for $x$: by (H1) $\Gamma_2(x)\cap R = \emptyset$, so $\{M(a): a\in\Gamma_2(x)\smallsetminus R\} =
\Gamma_2(M(x))$ by (H3); every element of the other type is incident with an element of $\Gamma_2(M(x))$ by (F3).
(E3) for $x$: $\{a\notin R: M(a)\in\Gamma_2(M(x))\} = \Gamma_2(x)$, which meets every element of $B(\tau_j)$ by (F3).
(E1): by (H1) no element of $B(\tau_j)$ has all its incident elements in $R$. $\square$

At $D = 7$ the analogous theorem also needed (H2), "$M(R)$ non-concurrent"; at $D = 5$ it follows from (H1), (H3)
anyway: for $x\ne y\in R$, $M(\{x,y\}^\perp) = \Gamma_2(M(x))\cap\Gamma_2(M(y))$ has $s+1$ elements, which is only
possible if $M(x),M(y)$ do not meet (two concurrent lines have $s-1$ common neighbours in $\Gamma_2$).

**Proposition 6.1 (local dualities preserve triad centres).** Under (H1), (H3), for pairwise non-collinear
$x,y,z\in R$: $|\{x,y,z\}^\perp| = |\{M(x),M(y),M(z)\}^\perp|$ (the right side counted in the dual).
*Proof.* $\{x,y,z\}^\perp = \Gamma_2(x)\cap\Gamma_2(y)\cap\Gamma_2(z)$, and $M$ is a bijection with
$M(\Gamma_2(\cdot)) = \Gamma_2(M(\cdot))$ on $R$. $\square$

**Corollary 6.2 ($q$ odd: two points at most).** Let $q$ be odd and let $M: P\to L$ be a bijection of $Q(4,q)$ (or of
$W(q)$). If $R$ satisfies (H1) and (H3) then $|R|\le 2$.
*Proof.* Three points of $R$ form a triad of points of $Q(4,q)$, which has 0 or 2 centres (Lemma 1.2(c)); their images
form a triad of lines of $Q(4,q)$, i.e. a triad of points of $W(q)$, which has 1 or $q+1$ centres. As $q+1\ge 4$, the
counts never agree, contradicting Proposition 6.1. The same argument with the roles exchanged works for $W(q)$. $\square$

This is the main difference from $D = 7$, where local dualities carried 81 to 768 freed points per transition. For
$q$ even there is a global duality and Theorem B applies instead.

**Proposition 6.4 (two points always work).** Let $x,y$ be non-collinear points and $\ell,m$ non-concurrent lines of a
GQ of order $(s,s)$. Define $M: P\to L$ by $M(x) = \ell$, $M(y) = m$, any bijection
$\{x,y\}^\perp\to\{\ell,m\}^\perp$, any bijection $\Gamma_2(x)\smallsetminus\{x,y\}^\perp\to\Gamma_2(\ell)\smallsetminus
\{\ell,m\}^\perp$, the same for $y,m$, and any bijection on the rest. Then (H1), (H3) hold for $R = \{x,y\}$, so the
transition is repaired.
*Proof.* The four sets $\{x,y\}$, $\{x,y\}^\perp$, $\Gamma_2(x)\smallsetminus\{x,y\}^\perp$, $\Gamma_2(y)\smallsetminus
\{x,y\}^\perp$ are pairwise disjoint (as $x,y$ are not collinear, $x\notin\Gamma_2(y)$), of sizes $2$, $s+1$,
$s^2-1$, $s^2-1$, and the same holds for the lines. So the pieces define a bijection between two subsets of the same
size, which extends to $P\to L$; (H3) holds by construction. $\square$

The program research/theorems/d5gq/localdual.py builds this $M$ (the "arbitrary" bijections in sorted order) and
confirms (E1)–(E3) and the brute force for $W(3), Q(4,3), W(5), Q(4,5)$.

**Computer-checked 6.5 (Theorem E goes beyond local dualities).** Squad card c4 found, by annealing, a bijection $M$
of $Q(4,5)$ and a freed set of **three** points that satisfies (E1)–(E3) (research/squads/gqd5-r1/c4/best.json; we
re-checked it with `exact_conditions` and `brute_bad`). Its triad has 2 centres and the image triad 1, so it is not a
local duality. No 4-point set was found ($q = 5$), and a SAT search for 3 points in $Q(4,3)$ did not finish in 600 s.

---

## 7. Relaxed freed sets of lines

In the typed layouts of §8 the binding constraint is the size $b$ of the freed sets of lines on friendly transitions
$D\to H$ (partial spreads of $Q(4,q)$, i.e. partial ovoids of $W(q)$). Here is how to free more lines.

Fix a friendly transition $t = (j\to j')$ with $\tau_j = D$, $\tau_{j'} = H$, $M_t = \mathrm{id}$, over $Q(4,q)$ (so
$A(\tau_j) = L$, $B(\tau_j) = P$, $A(\tau_{j'}) = P$, $B(\tau_{j'}) = L$). Let $T = R_t$ be a set of lines in which every
line meets at most one other line of $T$, its *partner*. For a partner pair $\ell, m$ let $z = \ell\cap m$.

**Proposition 7.1 (the bad pairs of a partner pair).** Inside levels $j,j'$, the pairs at distance $>5$ are exactly:
for every partner pair $(\ell,m)$, the pairs $((\ell,j),(p,j'))$ and $((p,j),(\ell,j'))$ with $p\in m\smallsetminus\{z\}$
(and the same with $\ell,m$ exchanged): $4q$ ordered pairs per partner pair.
*Proof.* Theorem E with $M = \mathrm{id}$. (E1) holds since no point lies on $q+1\ge 3$ lines of $T$. (E2) for $\ell$:
a point $v\notin\ell$ lies on exactly one line $\lambda(v)$ meeting $\ell$ (F4 dually), and is covered iff
$\lambda(v)\notin T$, i.e. $\lambda(v)\ne m$ (the only line of $T$ meeting $\ell$), i.e. $v\notin m\smallsetminus\{z\}$; a
point $v\in\ell$ lies on $q\ge 2$ lines of $\Gamma_2(\ell)$, at most one of them in $T$. The pairs that fail are
$((\ell,j),(v,j'))$, $v\in m\smallsetminus\{z\}$, by case (ii) of the proof of Theorem E. (E3) for $\ell$ is the same
statement for $B(\tau_j) = P$: the pairs $((v,j),(\ell,j'))$, $v\in m\smallsetminus\{z\}$, by case (v). Lines of $T$ without
partner satisfy (E2), (E3) as in Theorem B. $\square$

**Proposition 7.2 (the hub rule).** Suppose that for every line $\ell\in T$ with partner $m$:
- the $\mathcal B$-hub $h$ that takes the slot $(\ell,t)$ has its slot in level $j'$ at a point of $m$,
  $\omega_{j'}(h)\in m$; and
- the $\mathcal A$-hub $g$ that takes the slot $(\ell,t)$ (at $(\ell,j')$) has its slot in level $j$ at a point of $m$,
  $\omega'_j(g)\in m$.

Then every pair of Proposition 7.1 is at distance $\le 4$ in $X_R^+$.
*Proof.* $(\ell,j)\to h\to(\omega_{j'}(h),j')\to(n,j')\to(p,j')$ for $p\in m\smallsetminus\{z\}$, where $n = m$ if
$\omega_{j'}(h)\ne p$ (the two points lie on $m$): length $\le 4$. Likewise
$(\ell,j')\to g\to(\omega'_j(g),j)\to(m,j)\to(p,j)$. $\square$

In our layouts the natural slot on $m$ is the point $o_m$ where the ovoid $O$ (freed on the transition $H\to D$ out of
level $j'$, and on the $H\to D$ transitions into level $j$) meets $m$; $O$ meets every line exactly once. Requiring
$z\notin O$ makes $o_m\ne o_\ell$, and lines of $T$ through a common point of $O$ are not partners, so different
partnered lines ask for different points of $O$. Each such hub must exist, which bounds the number of partnered lines:
every partnered line uses one $\mathcal B$-hub slot per transition and one $\mathcal A$-hub (which can serve all
transitions out of level $j$ at once, since they all ask for $o_m$ in level $j$). In the $(13,5)$ graph this allows 14
partner pairs (§11).

In the language of $W(q)$ (lines of $Q(4,q)$ = points of $W(q)$, the ovoid $O$ = the spread of Lemma 1.1), $T$ is a set
of points of $W(q)$ in which every point is collinear with at most one other, and the line joining a collinear pair is
not in the spread. *Computer-checked*: research/theorems/d5gq/relaxed.c (annealing) finds such sets of size 58 for
$q = 9$ (56 with at most 14 pairs) and squad card r2c2 one of size 87 for $q = 11$, against 51 and 70 for partial
ovoids. Squad card r2c7 tested the rule independently at $q = 5$ (five levels $HHDHD$ over $Q(4,5)$, 23 freed lines with
6 partner pairs, $25+25$ hubs): with the hub rule the graph is valid (1,610 vertices, apsp), with the same sets and a hub
assignment ignoring the rule it has diameter 6 (research/squads/gqd5-r2/c7/).

---

## 8. Typed layouts and slot counts

By Theorem 3.5 the order is $(2r+1)\cdot 2N+K_{\mathcal A}+K_{\mathcal B}$ with $K_{\mathcal B}\le\min_j\alpha_j$ and
$K_{\mathcal A}\le\min_j\beta_j$. Over $Q(4,q)$, $q$ odd, write $a$ for the size of the freed sets on $H\to D$
transitions (points of $Q(4,q)$: an ovoid, $a = q^2+1$), $b$ for $D\to H$ (lines of $Q(4,q)$), $c$ for non-friendly
transitions ($c = 2$ by Proposition 6.4, $c\le 2$ for local dualities by Corollary 6.2).

**Proposition 8.1 (seven levels).** For the rotational tournament on $\mathbb Z_7$ ($j\to j+1,j+2,j+3$) with types
$HHHDHHD$:
$$\alpha = (a+2c,\ a+2c,\ a+2c,\ 2b+c,\ a+2c,\ a+2c,\ 3b),\qquad \beta = (b+2c,\ b+2c,\ b+2c,\ 3a,\ b+2c,\ b+2c,\ 2a+c).$$
So $\min\alpha = \min(a+2c,2b+c,3b)$ and $\min\beta = b+2c$; for $a+c\le 2b$, $K_{\mathcal A}+K_{\mathcal B}\le a+b+4c$.
*Proof.* Direct count: level 0 ($H$) has arcs to 1 ($H$), 2 ($H$), 3 ($D$), so $\alpha_0 = c+c+a$; level 3 ($D$) to
4, 5 ($H$), 6 ($D$): $b+b+c$; level 6 ($D$) to 0, 1, 2 ($H$): $3b$; and similarly for the others and for incoming arcs.
$\square$

*Computer-checked* (research/theorems/d5gq/layouts.py; squad card c15, research/squads/gqd5-r1/c15/formulas.md): over
all 2,640 labelled regular tournaments on 7 vertices and all typings, the largest $\min\alpha+\min\beta$ is
$\min(a+b+4c,\,3b+3c)$ for $a\ge b\ge c\ge 0$; for five levels it is $2b+2c$ (types $HHDHD$, Proposition 8.2 below); for
nine levels $4b+4c$ (exhaustive over the 15 isomorphism classes); for 11 and 13 levels sampling gives
$\min(2a+2b+6c,5b+5c)$ and $6b+6c$ (lower bounds only).

**Proposition 8.2 (five levels).** Rotational tournament on $\mathbb Z_5$, types $HHDHD$: $\alpha = (a+c, a+c, b+c,
a+c, 2b)$, $\beta = (b+c, b+c, 2a, b+c, a+c)$, so $\min\alpha = \min\beta = b+c$ when $b\le a$. (Direct count.)

With three levels some level has no friendly outgoing arc, so $K_{\mathcal A},K_{\mathcal B}\le c$.

For $q$ even we use instead all levels $H$ over $W(q)$, $M_t = \varphi|_P$ for a duality $\varphi$ on every arc and
$R_t = O_W$ an ovoid of $W(q)$ on every arc: every transition is repaired by Theorem B and
$\alpha_j = \beta_j = r(q^2+1)$.

---

## 9. Hub graphs

Write $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};\delta)$ for a bipartite graph with colour classes of sizes
$K_{\mathcal B}$, $K_{\mathcal A}$, maximum degree $\le\delta$, in which same-colour vertices are within distance 4.
If $Y$ is such a graph with $\delta\le q-r$, both conditions of Theorem 3.5 on $Y$ hold.

**Lemma 9.1 (explicit hub graphs).** $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};\delta)$ exists in each of the
following cases ($s$ a prime power):
- (Y0) $K_{\mathcal B},K_{\mathcal A}\le\delta$ (complete bipartite graph);
- (Y1) $s+1\le\delta$ and $s^2+s+1\le K_{\mathcal B},K_{\mathcal A}\le(s^2+s+1)(\delta-s)$;
- (Y2) $s+1\le\delta$ and $N(s)\le K_{\mathcal B},K_{\mathcal A}\le N(s)+(s+1)(\delta-s-1)$;
- (Y3) $K_{\mathcal B} = K_{\mathcal A} = (2r'+1)N(s)$ with $s+1+r'\le\delta$.

*Proof.* (Y0): distances 2. (Y1): the incidence graph of $\mathrm{PG}(2,s)$ (points as $\mathcal B$, lines as
$\mathcal A$; diameter 3, same-colour distance 2) with pendant vertices: up to $\delta-s-1$ new $\mathcal B$-vertices
on each line and new $\mathcal A$-vertices on each point. A pendant $p$ on $c$ and a core vertex $x$ of the colour of
$p$: $c$ and $x$ have different colours, $d(c,x)\le 3$, so $d(p,x)\le 4$. Two pendants of one colour hang on core
vertices of one colour, at distance $\le 2$: $d\le 4$. (Y2): the incidence graph of $W(s)$ (same-colour distance
$\le 4$, (Y1)) with up to $\delta-s-1$ pendant $\mathcal B$-vertices on each of the $s+1$ lines through a fixed point
$z_0$ and pendant $\mathcal A$-vertices on each of the $s+1$ points of a fixed line $m_0$: a pendant on a line $c$ and a
core point are within $1+3$; two pendants on lines through $z_0$ within $1+2+1$; dually. (Y3): the level graph of
Theorem A over $W(s)$ with $2r'+1$ levels has degree $s+1+r'$ and diameter 5, so same-colour distance $\le 4$. $\square$

Squad card c10 (research/squads/gqd5-r1/c10/table.md) tabulated the largest explicit balanced sizes (5, 15, 45, 120,
255, 468, 780, 1200, 2000, 2925, 4100 for $\delta = 2,\dots,12$, from (F3)), and found that random
$\delta$-regular bipartite graphs satisfy the condition up to about 271 vertices per colour at $\delta = 8$.
For the records we use a computer-found $Y$ (random degrees, then double-edge swaps that minimise the number of
same-colour hub pairs at distance $>4$ in $X_R^+$, paths through the levels counted; research/theorems/d5gq/hubopt.py),
and check the whole graph.

---

## 10. Families valid for every $q$

All ingredients below are explicit: the spread of Lemma 1.1 (an ovoid of $Q(4,q)$), the partial ovoid of Lemma 1.3,
the local dualities of Proposition 6.4, the hub graphs of Lemma 9.1, and for $q$ even a duality of $W(q)$.

**Corollary 10.1 ($q$ even, $1\le r\le q-1$).** Let all levels have type $H$ over $W(q)$, $M_t = \varphi|_P$ for a
duality $\varphi$, and $R_t = O_W$ an ovoid of $W(q)$ on every arc. Then for any $K_{\mathcal B},K_{\mathcal A}\le
r(q^2+1)$ for which an $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};q-r)$ exists (Lemma 9.1),
$$n_b(q+1+r,5)\ \ge\ (2r+1)\cdot 2N(q)+K_{\mathcal A}+K_{\mathcal B}.$$
*Proof.* Theorem B repairs every transition; Theorem 3.5 with $Y$ the hub graph. $\square$

**Corollary 10.2 ($q$ odd, five levels).** Types $HHDHD$ over $Q(4,q)$ (Proposition 8.2) with the ovoid $O$ on $H\to
D$, the lines of $Q(4,q)$ corresponding to the points of Lemma 1.3 on $D\to H$ ($b = 3q-1$, $q\ge 5$), Proposition 6.4
on the non-friendly arcs: for $K_{\mathcal A},K_{\mathcal B}\le 3q+1$ with an $\mathrm{HG}_5(K_{\mathcal B},
K_{\mathcal A};q-2)$,
$$n_b(q+3,5)\ \ge\ 10N(q)+K_{\mathcal A}+K_{\mathcal B}.$$

**Corollary 10.3 ($q$ odd, seven levels).** Types $HHHDHHD$ (Proposition 8.1), same ingredients: for
$K_{\mathcal B}\le\min(q^2+5,\,6q)$, $K_{\mathcal A}\le 3q+3$ with an $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};q-3)$,
$$n_b(q+4,5)\ \ge\ 14N(q)+K_{\mathcal A}+K_{\mathcal B}.$$

*Proofs.* Theorems B (friendly arcs: the ovoid is a partial ovoid, the set of Lemma 1.3 gives a partial spread of
$Q(4,q)$) and C/Proposition 6.4 (non-friendly arcs) repair every transition; slot counts from Propositions 8.1–8.2
with $a = q^2+1$, $b = 3q-1$, $c = 2$; Theorem 3.5. $\square$

**10.3 With computer-found sets.** Replacing $b$ by the size of a computer-found partial ovoid of $W(q)$ (Lemma 1.2(d)
bounds it by $q^2-q+1$) or a relaxed set (§7), and the hub graph by a computer-found one, gives the larger values of
§14. The best partial ovoids of $W(q)$ we found: 18 ($q=5$), 33 ($q=7$), 51 ($q=9$; four ILS runs and a group-orbit
search all stop at 50–51), 70 ($q=11$; tabu search; 68 from unions of orbits).

---

## 11. The $(13,5)$ record graph

**Corollary 11.1.** $n_b(13,5)\ge 11{,}626$.

*Construction* ($q = 9$, $r = 3$; research/theorems/d5gq/build_relaxed.py; solution file
research/theorems/d5gq/graphs/d13D5_q9_relaxed_n11626.json, edges ...n11626.edges.gz).
- $G = Q(4,9)$ as `W(9).dual()` (§1.2); levels $\mathbb Z_7$, rotational tournament, types $HHHDHHD$.
- $H\to D$ arcs ($0\to3$, $1\to3$, $2\to3$, $4\to6$, $5\to6$): $M = \mathrm{id}$, $R = O$, the ovoid of Lemma 1.1
  (82 points).
- $D\to H$ arcs ($3\to4$, $3\to5$, $6\to0$, $6\to1$, $6\to2$): $M = \mathrm{id}$, $R = T$, a relaxed set of 56 lines
  with 14 partner pairs (Proposition 7.2), listed in the solution file (`T`; also graphs/W9_relaxed_set_56.json as
  points of $W(9)$).
- The eleven non-friendly arcs ($0\to1$, $0\to2$, $1\to2$, $1\to4$, $2\to4$, $2\to5$, $4\to5$, $4\to0$, $5\to0$,
  $5\to1$ of type $H\to H$, and $3\to6$ of type $D\to D$): $M$ = the local duality of Proposition 6.4 on a
  two-element freed set, given in full in the solution file (`nonfriendly`).
- Slots: $\alpha = (86,86,86,114,86,86,168)$, $\beta = (60,60,60,246,60,60,166)$; $K_{\mathcal B} = 86$,
  $K_{\mathcal A} = 60$ hubs; the slot of every hub in every level is listed (`Bhub_slots`, `Ahub_slots`, as triples
  (level, element, arc)), chosen so that Proposition 7.2 holds for all 28 partnered lines.
- $Y$: 360 edges (`Y`), maximum degree 5 on the $\mathcal B$-side and $6 = q-r$ on the $\mathcal A$-side, found by
  hubopt.py.

Every transition is repaired (Theorems B, C and Proposition 7.2), (HG) holds (checked over the whole graph by the
builder), so Theorem 3.5 gives order $7\cdot 2\cdot 820+86+60 = 11{,}626$, maximum degree $13$. **Computer-checked**:
research/lifts/coordinator_check/apsp.c (BFS from every vertex) reports bipartite, degree max 13, diameter 5
(graphs/d13D5_q9_relaxed_n11626.check.txt). The neighbourhood of every vertex is determined by the solution file
through Definitions 2.1 and 3.1.

Earlier versions with a 51-point partial ovoid instead of the relaxed set: 11,605 (no local dualities) and 11,621
(graphs/d13D5_q9_typed_n11621.json).

---

## 12. Routing through a third level (computer experiments)

Theorem E is about two levels. With $2r+1\ge 5$ levels a pair $(u,j),(v,j')$ can also be joined through a third level
$i$ with two matching edges, e.g. $(x,j)\to(M_{j\to i}(x),i)\to(z,i)\to(M_{i\to j'}(z),j')\to(v,j')$ (length 4).
*Computer-checked* (squad cards):
- c19: seven levels over $Q(4,5)$, all type $H$: a **random** 16-point freed set on one non-friendly arc, violating
  (E2) and (E3), becomes harmless after annealing the other 20 matchings (apsp VALID, 2,184 vertices); five levels:
  8 points.
- c6: three levels over $Q(4,3)$: 5 freed points per transition with hubs (10 hubs, valid), all violating (E1)–(E3).

*Heuristic* (why this does not scale to $q = 11$): for a freed $x$ and a random $M$, about $N/e$ elements of the other
level violate (E2). A third level supplies about $(q+1)^2$ length-4 routes per freed element and per route type, so the
fraction of $A(\tau_{j'})$ left uncovered after the five other levels is about $e^{-1}e^{-5(q+1)^2/N}$: 12% for $q=5$
but 22% for $q = 11$, i.e. about 330 pairs per freed element to repair by deliberate changes, each change repairing
$q+1$ of them. We did not get third-level routing to work at $q\ge 9$.

---

## 13. Quadrangles of order $(s,t)$ with $s\ne t$

Proposition 2.2 rules out the level graph for $Q(5,q)$, $H(3,q^2)$ and $AS(q)$. Small experiments (squad cards c12,
c13; research/squads/gqd5-r1/c12, c13) tried the natural substitutes at the cells $\Delta = 5,7,9$:
- $GQ(2,4)$ at $\Delta = 5$: the 27 points already have degree 5, so only the 45 lines (2 spare edges each) can carry
  matchings, and the level structure must be bipartite (no odd cycles of levels). Best valid graph: 144 vertices
  (two levels), against the lab's 354.
- $AS(q)$ at $\Delta = q+2$: points have degree $q+2$ and lines degree $q$, so only lines have spare edges (two each),
  and line-to-line edges must join copies of opposite types. From a point $p$ of one copy, a point of another copy of the
  same type is at even distance, and a path of length 4 to it must be $p$, a line through $p$, a line of a copy of the
  other type, a line of the target copy, a point on it; so $p$ reaches at most $2(q+2)q$ such points, fewer than the
  $q^3$ points of one copy when $q\ge 5$ (*Theorem*, by this count). Hence for $q\ge 5$ at most one copy of each type
  can be used, and the order stays $\le 4q^2(q+1)$.
We found no construction from a quadrangle of unequal order that approaches the lab's values at $\Delta\le 9$.

---

## 14. Comparison with the 2013 table and the lab's values

"Theorem family" = Corollaries 10.1–10.3 (explicit sets and hub graphs; research/theorems/d5gq/family_table.py,
family_table_out.txt). "Computer" = the best graph of §§8–11 type that we built and checked by all-pairs BFS. "Lab" =
the lab's value before this note (README, research/RESULTS.md).

| cell | table (2013) | theorem family | computer (this note) | lab before | construction of the lab value |
|---|---:|---:|---:|---:|---|
| (10,5) | 4,000 | 4,044 ($q=7$, $r=2$) | 4,062 ($q=7$, $r=2$) | **4,800** | doubled-matching lift of $W(7)$ |
| (11,5) | 5,850 | 6,090 ($q=8$, $r=2$) | — | **7,020** | doubled-matching lift of $W(8)$ |
| (12,5) | 8,200 | 8,430 ($q=8$, $r=3$) | — | **9,840** | doubled-matching lift of $W(9)$ |
| (13,5) | 11,480 | 11,552 ($q=9$, $r=3$) | **11,626** | 11,486 | — |
| (14,5) | 14,760 | 14,812 ($q=9$, $r=4$) | — | **17,568** | doubled-matching lift of $W(11)$ |
| (15,5) | 20,496 | 20,598 ($q=11$, $r=3$) | 20,696 ($q=11$, $r=3$) | **20,736** | route-chart lift |
| (16,5) | 27,300 | 26,453 ($q=11$, $r=4$) | — | **33,792** | route-chart lift |

At $\Delta\le 9$ (cells $(5,5)$–$(9,5)$) the level graphs have $6N(q)$ or $10N(q)$ vertices for small $q$ (e.g.
$(9,5)$: $6N(7) = 2{,}400$, $(7,5)$: $6N(5) = 936$) and the hubs add only $O(q)$; they are below the 2013 table there,
and far below the lab's values.

**Why $(15,5)$ is out of reach here.** With seven levels over $Q(4,11)$ we have $K_{\mathcal B} = a+2c = 126$ and
$K_{\mathcal A} = b+2c$. The lab's value needs $K_{\mathcal A}+K_{\mathcal B}\ge 241$, so $b\ge 111 = q^2-q+1$, which is
Tallini's bound for partial ovoids of $W(11)$; the best partial ovoid we found has 70 points, and the best relaxed set
87 (with the hub budget allowing only about 21 partner pairs). By Proposition 8.1 and the computer search of §8, no other
typing of seven levels does better, and Corollary 6.2 caps local dualities at $c = 2$. So beating $(15,5)$ this way
needs either a non-friendly transition carrying many freed points (Theorem E allows more than local dualities, §6.5,
but we found only 3 at $q = 5$), or third-level routing at $q = 11$ (§12).

---

## 15. Computer checks

All graphs were checked with research/lifts/coordinator_check/apsp.c (all-pairs bit-parallel BFS, no symmetry): simple,
bipartite, maximum degree, exact diameter.

| graph | file (research/theorems/d5gq/) | result |
|---|---|---|
| $(13,5)$, $n = 11{,}626$ | graphs/d13D5_q9_relaxed_n11626.* | VALID, degree 13, diameter 5 |
| $(13,5)$, $n = 11{,}621$ | graphs/d13D5_q9_typed_n11621.* (json; rebuild with build_typed.py) | VALID |
| $(15,5)$-type, $q = 11$, $n = 20{,}696$ | build_typed.py 11 3 HHHDHHD with the 70-point set | VALID (beats the table, not the lab) |
| $(10,5)$-type, $q = 7$, $r = 2$, $n = 4{,}062$ | build_typed.py 7 2 HHDHD | VALID |
| $(8,5)$-type, $q = 5$, $r = 2$, $n = 1{,}596$ and $1{,}600$ | build_typed.py 5 2 HHDHD (and card c7 independently) | VALID |
| $(8,5)$-type, $q = 5$, relaxed line sets, $n = 1{,}610$ | squad card r2c7 (research/squads/gqd5-r2/c7/ld23.edges) | VALID; without the hub rule diameter 6 |
| 32 level graphs, $q\le 5$ | test_basic.py | all diameter 5 (Theorem A) |
| Theorem E vs brute force | test_basic.py | agree on 720 transitions |
| triads | triads.py | 0/2 in $Q(4,q)$, 1/$(q+1)$ in $W(q)$, $q = 3,5,7$ |
| local dualities | localdual.py | repaired, $q = 3,5$ |
| duality of $W(q)$, $q = 2,4,8$ | squad card c11 (research/squads/gqd5-r1/c11/) | verified; all-$H$ $q = 4$, $r = 1$: 544 VALID |

---

## 16. Prior art

- **The base graphs.** The cells $(10,5)$–$(15,5)$ of the 2013 table [MS13] are the level graphs of Theorem A; the
  CombinatoricsWiki table credits them to Delorme, Gómez and Quisquater ("On large bipartite graphs", submitted, not
  found). Compounds of a bipartite graph with a tournament go back to Gómez and Fiol [GF85]. Delorme [De85] §3 builds
  cyclic multi-level graphs from a duality of a quadrangle, and §7–8 duplicates sets of vertices of a quadrangle's
  incidence graph (an ovoid/spread copy at $D = 4$). We claim none of these.
- **Hubs and deleted matching edges.** R. Rajiv (Zenodo, 30 Sept 2026, doi 10.5281/zenodo.23052995) deletes the edges
  of a type-preserving matching at a set of pairwise non-collinear points of a compound of generalized-polygon incidence
  graphs and attaches new vertices joined by a graph of diameter $\le n$, for general (non-bipartite) graphs of diameter
  $n = 4, 6$. Our friendly transitions with Theorem B are the bipartite, diameter $n+1$ version of that step, and our
  hubs are one-sided. The lab's literature check (research/lit/novelty-2026-10-25.md, branch
  claude/novelty-literature-check-4i5frp) found nothing on: an exact criterion like Theorem E, local dualities
  (Theorem C) and their two-point limit for $q$ odd (Corollary 6.2), relaxed freed sets with the hub rule (§7). That
  check was done for the hexagon case; we did not repeat it for quadrangles, so "nothing found" applies only to those
  sources.
- **The lab's earlier $D = 5$ work.** The doubled-matching lifts of $W(q)$ (research/d10D7/DM_D5.md) give $12N(q)$ at
  degree $q+3$ and are better than everything here for $\Delta = 10, 11, 12, 14$. The previous $(13,5)$ value 11,486 was
  $7\cdot 2N(9)+6$ (research/cell147/).
- **Finite geometry used.** Payne–Thas [PT] for all facts on quadrangles; Tallini [Ta91] and Klein–Metsch [KM] for
  partial ovoids/spreads; Ceria–De Beule–Pavese–Smaldore [CDPS] for large partial ovoids of $W(3,q)$.

**References.**
[CDPS] M. Ceria, J. De Beule, F. Pavese, V. Smaldore, *On large partial ovoids of symplectic and Hermitian polar spaces*,
J. Combin. Des. 31 (2023) 5–22, arXiv:2203.04553.
[De85] C. Delorme, *Grands graphes de degré et diamètre donnés*, European J. Combin. 6 (1985) 291–302.
[GF85] J. Gómez, M. A. Fiol, *Dense compound graphs*, Ars Combin. 20-A (1985) 211–237.
[KM] A. Klein, K. Metsch, results on partial spreads of $Q(4,q)$ as quoted in the survey of De Beule, Klein, Metsch,
Storme, *Partial ovoids and partial spreads of classical finite polar spaces*, Serdica Math. J. 34 (2008).
[MS13] M. Miller, J. Širáň, *Moore graphs and beyond: a survey of the degree/diameter problem*, Electron. J. Combin.
DS14v2 (2013).
[PT] S. E. Payne, J. A. Thas, *Finite Generalized Quadrangles*, 2nd ed., EMS, 2009.
[Ta91] G. Tallini, *Blocking sets with respect to planes in PG(3,q) and maximal spreads of a nonsingular quadric in
PG(4,q)*, Mitt. Math. Sem. Giessen 201 (1991) 141–147.
