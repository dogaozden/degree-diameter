# Bipartite graphs of diameter 5 from generalized quadrangles: level graphs, surgery and hubs

Draft of 26 October 2026, written for Ignacio López and Gabriela Araujo-Pardo by the degree–diameter lab
(github.com/dogaozden/degree-diameter; Claude Code sessions coordinated by Doğa Özden). Job "thm-gq-d5". Revised 28 October
2026 (job "d5-relax"): the record status and the prior art corrected after the referee report
research/referee/d5-quadrangle.md (branch claude/referee-d5-quadrangle-621u7o), and §7 without the condition that partners
meet off the ovoid (Lemma 7.3), with new searches (§7, §14).

This note does for diameter 5 and generalized quadrangles what research/theorems/D7_HEXAGON.md (branch
claude/d7-hexagon-theorems-4w1prt) does for diameter 7 and the split Cayley hexagon: $2r+1$ copies of the incidence graph
of a generalized quadrangle of order $(q,q)$, joined by perfect matchings, have diameter 5; deleting some matching edges
and attaching new "hub" vertices to the freed ends adds vertices. We state exactly which deletions survive, prove it,
and give the resulting families. With explicit ingredients they beat the 2013 table in the six cells $(10,5)$–$(15,5)$;
none of them reaches the lab's current values (§14).

Every claim is labelled **Theorem** (with a complete proof here), **Computer-checked** (a computation, with the program
and its output in the repository), or **Heuristic** (an estimate, no proof). The neighbourhood of every vertex of every
graph is given explicitly (Definitions 2.1 and 3.1, and for the computer-found graphs their solution files).

*File paths* refer to the repository github.com/dogaozden/degree-diameter, branch claude/gq-diameter-5-xa5d3d (this
revision: branch claude/d5-relax-searches-osr72a). The tools are in research/theorems/d5gq/, and those of the revision in
research/theorems/d5relax/; the Haiku squad rounds that searched for sets and ran small-$q$ tests are in
research/squads/gqd5-r1/, gqd5-r2/, gqd5-r3/ and d5relax-r1/ (log: research/squads/LOG.md).

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
11. A $(13,5)$ graph on 11,636 vertices
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
$(13,5) = 7\cdot 2N(9)$, $(14,5) = 9\cdot 2N(9)$, $(15,5) = 7\cdot 2N(11)$. The CombinatoricsWiki credits these cells to
Delorme, Gómez and Quisquater [DGQ] (§16).

**A $(13,5)$ graph on 11,636 vertices** (table 11,480). It is not a record: when this note was first written the lab's
value was 11,486, but since 26 October the lab has $(13,5) = 11{,}700$, a multi-doubled-matching lift of $W(8)$ (§16), and
§14 shows that no graph of this note's kind can reach 11,700. The graph: seven levels over
$Q(4,9)$ and its dual $W(9)$, an ovoid freed on five transitions, a computer-found set of 66 lines with 30 concurrent
pairs freed on five more, two-point local dualities on the other eleven, $86+70$ hubs (§11). It was checked by a
breadth-first search from every vertex (§15).

**Theorems.**

- **Theorem A** (§2; these graphs have the orders of the table values): any typing, any bijections: diameter $\le 5$.
- **Theorems 3.5, 3.6** (assembly): if every transition is *repaired* (or, more generally, every two levels are within
  distance 5 of each other), same-colour hubs are within distance 4 and the hub graph has maximum degree $\le q-r$, then
  $n_b(q+1+r,5)\ge (2r+1)\cdot 2N + K_{\mathcal A}+K_{\mathcal B}$.
- **Theorem E** (§4): a transition with matching $M$ and freed set $R$ is repaired **if and only if** two covering
  conditions (E2), (E3) hold. This is new compared with the $D=7$ note, where only sufficient conditions were given.
  (The letter E stands for "exact"; there is no Theorem D.)
- **Theorem B** (§5): a transition whose matching extends to an automorphism (the identity between a quadrangle and its
  dual, or a duality) is repaired if and only if its freed set is a **partial ovoid** (resp. partial spread). The
  "segment sets" of the hexagon do not survive at $D=5$.
- **Theorem C** (§6): a local duality on a non-collinear freed set repairs a transition; at $D=5$ the condition on
  $M(R)$ is not needed. **Corollary 6.2**: for $q$ odd, a local duality between $Q(4,q)$ and itself (or $W(q)$ and
  itself) exists on at most **two** points, because point triads of $Q(4,q)$ have 0 or 2 centres and line triads 1 or
  $q+1$. **Proposition 6.4**: two points always work.
- **Proposition 7.2** (§7): freed lines may come in concurrent pairs if the $\mathcal A$-hub at the slot of each line
  sits at a point of its partner (e.g. the ovoid point). **Lemma 7.3**: in the seven-level layout such hubs always
  exist, also when partners meet at a point of the ovoid.
- **Proposition 14.1** (§14): ceilings of the construction per cell; only $(15,5)$ is within reach, and it needs a
  relaxed set of 111 points of $W(11)$ (we found 89).
- **Families** (§10, Corollaries 10.1–10.4), valid for every $q$, with explicit sets and explicit hub graphs. For
  example, for $q$ odd, $q\ge 5$: $n_b(q+4,5)\ge 14N(q)+K_{\mathcal A}+K_{\mathcal B}$, where the explicit sets allow
  up to $6q$ and $3q+3$ hubs and the explicit hub graphs of Lemma 9.1 decide how many are used. With
  those hub graphs the families exceed the 2013 table in the cells $(10,5)$–$(15,5)$ (§14).

**What does not work** (§§12–14): the level-graph family stays below the lab's values (doubled-matching lifts,
route-chart lifts and the multi-doubled-matching lift at $(13,5)$) in every cell $(10,5)$–$(16,5)$, and far below at
$\Delta\le 9$. Proposition 14.1 shows that only $(15,5)$ is within reach of the construction at all: it needs a relaxed
set of 111 points of $W(11)$. The best graph of this kind we built there has 20,715 vertices (relaxed set of 89 lines
of $Q(4,11)$, Computer-checked 7.4), 21 short of the lab's 20,736.

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
(d) (Tallini [Ta91]) A partial ovoid of $W(q)$, $q$ odd, has at most $q^2-q+1$ points; equivalently a partial spread
of $Q(4,q)$, $q$ odd, has at most $q^2-q+1$ lines.

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
partial ovoids for specific $q$ (§10.3): 18 ($q=5$), 33 ($q=7$), 51 ($q=9$), 70 ($q=11$). *Computer-checked* (squad card
r2c8, research/squads/gqd5-r2/c8/results.md): 18 is the maximum for $W(5)$ (no 19-point partial ovoid: SAT, two solvers,
using the transitivity of $\mathrm{PSp}(4,5)$ on non-collinear pairs), below Tallini's bound 21. We know no explicit family
of order $q^2$ for $q$ odd; Ceria, De Beule, Pavese and Smaldore [CDPS] construct large partial ovoids of $W(3,q)$ for
$q$ an odd square with $3\nmid q$ (we did not compare sizes with ours).

**Lemma 1.4 (an explicit duality of $W(q)$, $q$ even).** For a line $\ell = \langle x,y\rangle$ of $W(q)$ put
$\psi(\ell) = (p_{01},p_{03},p_{23},p_{12})$ (Plücker coordinates as above), and for a point $x$ let $\varphi(x)$ be
the set $\{\psi(\ell): x\in\ell\}$. For $q$ even, $\psi$ is a bijection from the lines to the points of $W(q)$,
each $\varphi(x)$ is a line of $W(q)$, and $x\in\ell\iff\psi(\ell)\in\varphi(x)$; so $(\varphi,\psi)$ is a duality.
*Proof.* By §1.2, $\ell\mapsto X = (p_{01},p_{23},p_{02},p_{03},p_{12})$ maps the lines of $W(q)$ onto the points of
$Q(4,q)$: $X_0X_1+X_2^2+X_3X_4 = 0$, and the pencil of lines through $x$ onto a line of $Q(4,q)$. For $q$ even the polar
form $X_0Y_1+X_1Y_0+X_3Y_4+X_4Y_3$ has radical $\langle e_2\rangle$ (the nucleus), and projecting from $e_2$,
$X\mapsto(X_0,X_3,X_1,X_4) = \psi(\ell)$, maps $Q(4,q)$ bijectively onto $\mathrm{PG}(3,q)$ and lines of $Q(4,q)$ onto
lines that are totally isotropic for $y_0y_2'+y_2y_0'+y_1y_3'+y_3y_1'$, which is $w$ in characteristic 2 [PT, 3.2.1].
Composing gives the claim. $\square$ *Computer-checked* for $q = 2,4,8$ (all incidences); squad card c11 built the same
duality another way. The image $O_W = \psi(\text{spread of Lemma 1.1})$ is then an ovoid of $W(q)$.

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

With all types $H$, one bijection $\sigma:P\to L$ on every arc and $(s,s) = (q,q)$ these graphs have the orders of the 2013
table values listed in §0 (two plain matchings over $\mathbb Z_5$, three over $\mathbb Z_7$, four over $\mathbb Z_9$).

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

(In all our constructions every hub has one neighbour in every level; Lemma 3.4 uses this. A hub cannot be joined to an
$\mathcal A$-vertex of one level and a $\mathcal B$-vertex of another: all $\mathcal A$-vertices have one colour, so this
would break bipartiteness, as squad card c17 also found by experiment.)

**Lemma 3.2 (one matching edge).** Let $t = (j\to j')$. A simple path of length $\le 5$ from level $j$ to level $j'$ that uses
only level edges of $j,j'$ and remaining matching edges of $t$ uses exactly one matching edge.
*Proof.* It uses an odd number of them. With three or more, write the path as
$(u,j)\leadsto(a_1,j)\to(M(a_1),j')\leadsto(M(a_2),j')\to(a_2,j)\leadsto(a_3,j)\to\cdots$. A simple path does
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

**Theorem 3.6 (assembly, general form).** Theorem 3.5 remains true if (T) is replaced by

- (T') for every arc $t = (j\to j')$, every vertex of level $j$ is within distance 5 of every vertex of level $j'$ in
  $X_R^+$.

*Proof.* The same; (T) implies (T') because $X_R$ is a subgraph of $X_R^+$. $\square$

We use (T') for transitions that are repaired only with the help of hubs (§7) or of other levels (§12).

---

## 4. Theorem E: the exact criterion

**Theorem E.** Let $t = (j\to j')$ be any transition of a level graph over a GQ of order $(s,s)$, $M = M_t$,
$R = R_t\subseteq A(\tau_j)$, $R\ne\emptyset$. Then $t$ is repaired if and only if

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
all pairs iff (E1): *it is not the case that some element of $B(\tau_j)$ has all its incident elements in $R$ and some
element of $A(\tau_{j'})$ has all its incident elements in $M(R)$.* And (E2) implies (E1): if $\Gamma_1(v)\subseteq M(R)$
for some $v\in A(\tau_{j'})$, no $a\notin R$ has $M(a)$ incident with $v$, so (E2) fails for every $x\in R$.

(v) $u\in B(\tau_j)$, $v\in B(\tau_{j'})$: $d(u,a)$ odd, $d(M(a),v)$ even; total $\le 4$ means $(1,0),(1,2)$ or $(3,0)$.
If $v\notin M(R)$, $a = M^{-1}(v)$ works ($3+0$). If $v = M(x)$, $x\in R$: $d(M(a),v) = 0$ would force $a = x$, so we
need $a\in\Gamma_1(u)\smallsetminus R$ with $M(a)\in\Gamma_2(M(x))$; for all $u$ this is (E3) for $x$.

These cases cover all pairs ($u\in A\smallsetminus R$: (i); $u\in R$: (ii),(iii); $u\in B$: (iv),(v)). $\square$

(If $R = \emptyset$ the transition is repaired by Theorem A.)

*Computer-checked*: test_basic.py compares the conditions of Theorem E (repair.py, `exact_conditions`, which also tests (E1)) with a brute-force evaluation of
(3.1) over all pairs (repair.py, `brute_bad`): 30 random friendly and non-friendly transitions for each $q = 2,3,4,5$,
and 300 transitions with whole lines and pencils inside $R$ for $q = 2,3$ (transitions failing only (E2), only (E3), and both occur); they agree in
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
statement. $\square$

(A friendly transition whose matching is a collineation, restricted to points or to lines, is also automorphic; Theorem B
covers it too.)

So at $D = 5$ the freed sets of automorphic transitions are exactly the partial ovoids; there is no analogue of the
hexagon's segment sets (a pair of collinear freed points already breaks the transition). For $W(q)$ and $Q(4,q)$ the
largest are the ovoids, $q^2+1$ points, when they exist (Lemma 1.2(a)).

*Computer-checked*: test_basic.py, 30 random sets per $q\le 5$ (half partial ovoids, half not): repaired iff partial
ovoid. Squad card c9 built a three-level graph over $Q(4,5)$ with an 18-line partial spread plus one line meeting two of
its lines on a friendly transition, and no hubs: Theorem B says the transition is not repaired, and in this example the third level does not repair it
either: diameter 6.

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
(E3) for $x$: $\{a\notin R: M(a)\in\Gamma_2(M(x))\} = \Gamma_2(x)$, which meets every element of $B(\tau_j)$ by (F3). $\square$

At $D = 7$ the analogous theorem also needed (H2), "$M(R)$ non-concurrent"; at $D = 5$ it follows from (H1), (H3)
anyway: for $x\ne y\in R$, $M(\{x,y\}^\perp) = \Gamma_2(M(x))\cap\Gamma_2(M(y))$ has $s+1$ elements, which is only
possible if $M(x),M(y)$ do not meet (two concurrent lines have $s-1$ common neighbours in $\Gamma_2$).

**Proposition 6.1 (local dualities preserve triad centres).** Under (H1), (H3), for pairwise non-collinear
$x,y,z\in R$: $|\{x,y,z\}^\perp| = |\{M(x),M(y),M(z)\}^\perp|$ (the right side counted in the dual).
*Proof.* $\{x,y,z\}^\perp = \Gamma_2(x)\cap\Gamma_2(y)\cap\Gamma_2(z)$, and $M$ is a bijection with
$M(\Gamma_2(\cdot)) = \Gamma_2(M(\cdot))$ on $R$. $\square$

**Corollary 6.2 ($q$ odd: two points at most).** Let $q$ be odd and let $M: P\to L$ be a bijection of $Q(4,q)$ (or of
$W(q)$). If $R$ satisfies (H1) and (H3) then $|R|\le 2$.
*Proof.* Three points of $R$ are pairwise non-collinear by (H1), so they form a triad of points of $Q(4,q)$, which has 0
or 2 centres (Lemma 1.2(c)). Their images are pairwise non-concurrent (remark after Theorem C), so they form a triad of
lines of $Q(4,q)$; under $Q(4,q)\cong W(q)^D$ this is a triad of points of $W(q)$ whose centres are the lines of $Q(4,q)$
meeting all three, and it has 1 or $q+1$ centres. As $q+1\ge 4$, the counts never agree, contradicting Proposition 6.1.
The same argument with the roles of $W(q)$ and $Q(4,q)$ exchanged works for $W(q)$. A $D\to D$ transition over $Q(4,q)$
is a bijection from the lines to the points of $Q(4,q)$, i.e. from the points to the lines of $W(q)$, and is covered by
the $W(q)$ case. $\square$

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
confirms (E2), (E3) and the brute force for $W(3), Q(4,3), W(5), Q(4,5)$.

**Computer-checked 6.5 (Theorem E goes beyond local dualities).** Squad card c4 found, by annealing, a bijection $M$
of $Q(4,5)$ and a freed set of **three** points that satisfies (E2), (E3) (research/squads/gqd5-r1/c4/best.json; we
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
*Proof.* We go through the cases of the proof of Theorem E with $M = \mathrm{id}$ and $R = T$. Case (i) is always fine.
Case (iv): a point $v$ of level $j'$ lies on $q+1\ge 3$ lines, at most two of them in $T$, so some line through $v$ is
not in $M(T) = T$. Lines of $T$ without partner: $\Gamma_2(\ell)\cap T = \emptyset$, and cases (ii), (iii), (v) hold
as in Theorem B. Now let $\ell$ have partner $m$, $z = \ell\cap m$.
Case (ii), $u = (\ell,j)$ and $v$ a point of level $j'$: a point $v\notin\ell$ lies on exactly one line $\lambda(v)$
meeting $\ell$ ((F4) dually), and $v$ is incident with an element of $\Gamma_2(\ell)\smallsetminus T$ iff
$\lambda(v)\ne m$ (the only line of $T$ meeting $\ell$), i.e. iff $v\notin m\smallsetminus\{z\}$; a point $v\in\ell$ lies
on $q\ge 2$ lines of $\Gamma_2(\ell)$, at most one of them in $T$. So exactly the pairs $((\ell,j),(v,j'))$,
$v\in m\smallsetminus\{z\}$, fail.
Case (iii), $u = (\ell,j)$ and $v$ a line of level $j'$: $v$ has a point $w\notin m\smallsetminus\{z\}$ (if $v\ne m$, $v$
meets $m$ in at most one point; if $v = m$ take $w = z$). By case (ii) some $a\in\Gamma_2(\ell)\smallsetminus T$ is
incident with $w$, and $d(\ell,a)+d(a,v)\le 2+2$: fine.
Case (v), $v = (\ell,j')$ and $u$ a point of level $j$: we need a line $a\notin T$ through $u$ meeting $\ell$; by the same
count this exists iff $u\notin m\smallsetminus\{z\}$. So exactly the pairs $((u,j),(\ell,j'))$, $u\in m\smallsetminus\{z\}$,
fail. $\square$

**Proposition 7.2 (the hub rule).** Suppose that for every line $\ell\in T$ with partner $m$, the $\mathcal B$-slot
$(\ell,t)$ (at the vertex $(\ell,j')$) is taken by an $\mathcal A$-hub $g_\ell$ whose slot in level $j$ is at a point of
$m$: $\omega'_j(g_\ell)\in m$. Then every pair of Proposition 7.1 is at distance $\le 4$ in $X_R^+$. (Nothing is assumed
about the meeting point $z = \ell\cap m$.)

*Proof.* Let $p\in m\smallsetminus\{z\}$. The pair $((p,j),(\ell,j'))$:
$(\ell,j')\to g_\ell\to(\omega'_j(g_\ell),j)\to(m,j)\to(p,j)$, a path of length $\le 4$ (shorter if
$\omega'_j(g_\ell) = p$). The pair $((\ell,j),(p,j'))$: the partner of $m$ is $\ell$, so the hub $g_m$ of the slot
$(m,t)$ sits at $(m,j')$ and, in level $j$, at a point $\omega'' = \omega'_j(g_m)$ of $\ell$; hence
$(\ell,j)\to(\omega'',j)\to g_m\to(m,j')\to(p,j')$ has length 4. $\square$

So a transition with a relaxed set is not repaired in the sense of Definition 3.3, but with the hub rule it satisfies
(T') of Theorem 3.6. (An earlier version of this note also asked the $\mathcal B$-hub of the slot $(\ell,t)$ to sit, in
level $j'$, on $m$; the second path above shows that this is not needed. We found this when a graph violating that
condition for 128 slots passed the all-pairs check.)

*The hubs exist.* In our layouts the natural slot on $m$ is the $\mathcal B$-slot at the point $o_m$ where the ovoid
$O$ meets $m$ ($O$ meets every line exactly once), freed on an $H\to D$ transition into level $j$. For the seven-level
layout no condition on the meeting points is needed:

**Lemma 7.3 (hub assignment).** Take the layout $HHHDHHD$ of Proposition 8.1 over $Q(4,q)$ with $M = \mathrm{id}$ and
$R = O$, an ovoid, on the five $H\to D$ arcs, $M = \mathrm{id}$ and one relaxed set $T$ on the five $D\to H$ arcs, and any
freed sets on the non-friendly arcs, and let $|T|\le K_{\mathcal A}\le\min_j\beta_j$. Then the $\mathcal A$-hubs can be
placed so that the hypothesis of Proposition 7.2 holds on all five $D\to H$ arcs, whatever the meeting points of the
partner pairs. In particular two partners may meet at a point of $O$.

*Proof.* Give every $\ell\in T$ its own $\mathcal A$-hub $g_\ell$. Every $H$-level receives exactly one arc from a
$D$-level (levels 4, 5 from 3; levels 0, 1, 2 from 6), so $g_\ell$ can take the slot $(\ell,t)$ of all five
$D\to H$ arcs $t$, one in each of the levels 4, 5, 0, 1, 2. If $\ell$ has a partner $m$, let $g_\ell$ take, in level 3
and in level 6, a free $\mathcal B$-slot at the point $o_m$. Then $\omega'_3(g_\ell) = \omega'_6(g_\ell) = o_m\in m$,
which is the hypothesis of Proposition 7.2 for the arcs $3\to4$, $3\to5$ (source level 3) and $6\to0$, $6\to1$, $6\to2$
(source level 6). These requests can be met. A point $o\in O$ carries the free $\mathcal B$-slots $(o,0\to3)$,
$(o,1\to3)$, $(o,2\to3)$ in level 3 and $(o,4\to6)$, $(o,5\to6)$ in level 6. The hub $g_\ell$ asks for $o$ iff $o$ lies
on the partner of $\ell$, and partnering is an involution, so the number of hubs asking for $o$ equals the number of
partnered lines of $T$ through $o$. At most two lines of $T$ pass through a point (a third would meet two others). So
every point of $O$ is asked for at most twice in each $D$-level, and it has three slots in level 3 and two in level 6.
(The case of two requests is a partner pair $\ell, m$ meeting at $z = o\in O$: then $o_m = o_\ell = z$, and both
$g_\ell$ and $g_m$ sit at $z$, which lies on both lines.) The remaining slots are unconstrained. In an $H$-level the
$|T|$ hubs $g_\ell$ take the $|T|$ slots of $T$, and the other $K_{\mathcal A}-|T|\le\beta_j-|T|$ hubs take slots of the
non-friendly arcs; in levels 3 and 6 the hubs without a request take any of the remaining $\beta_j$ minus the requested
slots. $\square$

The $\mathcal B$-hubs are not constrained at all. So one $\mathcal A$-hub per line of $T$ suffices: one hub serves its
line on the transitions out of both $D$-levels, because in $HHHDHHD$ the $D\to H$ arcs out of different $D$-levels end
in different levels. (An earlier version of this paragraph asked for one hub per partnered line *and per $D$-level*, and
required $z\notin O$ for every partner pair so that distinct partnered lines would ask for distinct points. Neither is
needed here.) The condition $z\notin O$ is needed when a $D$-level with $D\to H$ arcs out of it receives a single
$H\to D$ arc, so that a point of $O$ carries one free $\mathcal B$-slot there: level 4 of the five-level layout $HHDHD$
(in-arcs $2\to4$, which is $D\to D$, and $3\to4$). In the nine-level layout $HHHHDHHHD$ the two $D$-levels receive four
and three $H\to D$ arcs, and the proof of Lemma 7.3 goes through unchanged.

In the language of $W(q)$ (lines of $Q(4,q)$ = points of $W(q)$, the ovoid $O$ = the spread $S$ of Lemma 1.1), $T$ is a
set of points of $W(q)$ in which every point is collinear with at most one other; by Lemma 7.3 the line joining a
collinear pair may be any line, also a line of $S$ (a pair meeting at $z\in O$ is a pair on the spread line $z$). The
searches before Lemma 7.3 also required the joining line not to be in $S$; then $T$ has at most one point on each line
of $S$, so $|T|\le q^2+1$. In general, every point of $W(q)$ lies on one line of $S$ and $q$ others, and a line holds at
most two points of $T$, two only for a pair; so with $p_S$ pairs on lines of $S$ and $p_N$ on other lines,
$|T|-p_S\le q^2+1$ and $q|T|-p_N\le q(q^2+1)$. With $|T|\ge 2(p_S+p_N)$ this gives
$|T|\le 2(q+1)(q^2+1)/(2q+1)$ (the plain count: a single point uses $q+1$ lines, a pair $2q+1$, no line is shared), i.e.
at most 28, 53, 86, 127 for $q = 5,7,9,11$.

*Computer-checked* (research/theorems/d5relax/; squad round d5relax-r1). Largest relaxed sets found, with the spread
condition / without it:

| $q$ | counting bound | partial ovoid (best known to us) | relaxed, with the condition | relaxed, without it |
|---:|---:|---:|---:|---:|
| 3 | 11 | 7 | 10 (exact) | 11 (exact, MIP) |
| 5 | 28 | 18 (exact) | 23 (exact, card r2c8) | 23 (found; 24 undecided) |
| 7 | 53 | 33 | 41 | 41 |
| 9 | 86 | 51 | 66 | 66 |
| 11 | 127 | 70 | 88 | 89 (36 pairs, 4 on lines of $S$) |
| 13 | 176 | — | — | 103 (short run) |

The values without the condition come from our tabu search (rtabu.c) and were checked independently (score.py, which
recomputes collinearity from coordinates). At $q = 11$ eight different strategies of the squad stop at 89: weighted
local search, unions of orbits of 533 subgroups of $\mathrm{Sp}(4,11)$ solved exactly (best 81, then 89 by tabu search),
sets with all pairs on lines of $S$ (74 in the restricted model, 89 after an unrestricted search), large-neighbourhood
search with exact MIP re-optimisation (regions of 700–1000 points solve to optimality and never pass 89), seeded growth
from partial ovoids and torus orbits, and algebraic families. Two of the 89-point sets share only two points, so 89 is
a broad plateau rather than one basin. So dropping the condition gains one point at $q = 11$ and none at $q = 7, 9$ in
these searches. The cyclic subgroups of order $(q^2+1)/2 = 61$, the natural symmetry for a set with two points on half
of the spread lines (which could reach $q^2+1 = 122$), have no relaxed orbit at all (c61.py). Relaxed *point* sets of
$Q(4,q)$, the dual question for the $H\to D$ arcs, did not exceed the ovoid size in the tabu searches (10 at $q = 3$,
26 at $q = 5$).

**Computer-checked 7.4 (Lemma 7.3 at full size).** The seven-level graph over $Q(4,11)$ with the 89-point relaxed set
above (36 pairs, 4 of them meeting at ovoid points; research/theorems/d5relax/graphs/W11_relaxed_set_89.txt), built by
research/theorems/d5relax/build_zo.py with the hub assignment of Lemma 7.3, $K_{\mathcal B} = 126$,
$K_{\mathcal A} = 93$, has 20,715 vertices, maximum degree 15 and diameter 5 (apsp_mt, BFS from every vertex;
graphs/d15D5type_q11_zo89.*). The hub rule holds at all $5\cdot 72 = 360$ instances. The solution file was rebuilt
independently by research/theorems/d5gq/sol2edges.py and by the referee's research/referee/d5_checks/rebuild_record.py
(which re-checks every hypothesis); both give the same edge set. With the level-3 slot of one hub of a pair meeting at
an ovoid point moved off its partner (`BREAK=1`), the graph has diameter 6.

Squad card r2c7 tested the rule independently at $q = 5$ (five levels $HHDHD$ over $Q(4,5)$, 23 freed lines with
6 partner pairs, $25+25$ hubs): with the hub rule the graph is valid (1,610 vertices, apsp), with the same sets and a hub
assignment ignoring the rule it has diameter 6 (research/squads/gqd5-r2/c7/). Card r3c4 tested the final form (only
the $\mathcal A$-hub condition, $\mathcal B$-hubs placed arbitrarily, many partner pairs): five levels over $Q(4,5)$ with
23 lines and 6 pairs (1,610 vertices) and over $Q(4,7)$ with 41 lines and 15 pairs (4,086 vertices) are valid, and moving
the level-$j$ slot of one $\mathcal A$-hub off the partner line gives diameter 6 in both cases
(research/squads/gqd5-r3/c4/).

---

## 8. Typed layouts and slot counts

By Theorem 3.5 the order is $(2r+1)\cdot 2N+K_{\mathcal A}+K_{\mathcal B}$ with $K_{\mathcal B}\le\min_j\alpha_j$ and
$K_{\mathcal A}\le\min_j\beta_j$. Over $Q(4,q)$, $q$ odd, write $a$ for the size of the freed sets on $H\to D$
transitions (points of $Q(4,q)$: an ovoid, $a = q^2+1$), $b$ for $D\to H$ (lines of $Q(4,q)$), $c$ for non-friendly
transitions ($c = 2$ by Proposition 6.4, $c\le 2$ for local dualities by Corollary 6.2).

Below $a\ge b\ge c\ge 0$.

**Proposition 8.1 (seven levels).** For the rotational tournament on $\mathbb Z_7$ ($j\to j+1,j+2,j+3$) with types
$HHHDHHD$:
$$\alpha = (a+2c,\ a+2c,\ a+2c,\ 2b+c,\ a+2c,\ a+2c,\ 3b),\qquad \beta = (b+2c,\ b+2c,\ b+2c,\ 3a,\ b+2c,\ b+2c,\ 2a+c).$$
So $\min\alpha = \min(a+2c,2b+c,3b)$ and $\min\beta = b+2c$ (as $b+c\le 2a$); for $a+c\le 2b$, $K_{\mathcal A}+K_{\mathcal B}\le a+b+4c$.
*Proof.* Direct count: level 0 ($H$) has arcs to 1 ($H$), 2 ($H$), 3 ($D$), so $\alpha_0 = c+c+a$; level 3 ($D$) to
4, 5 ($H$), 6 ($D$): $b+b+c$; level 6 ($D$) to 0, 1, 2 ($H$): $3b$; and similarly for the others and for incoming arcs.
$\square$

*Computer-checked* (research/theorems/d5gq/layouts.py; squad card c15, research/squads/gqd5-r1/c15/formulas.md): over
all 2,640 labelled regular tournaments on 7 vertices and all typings, the largest $\min\alpha+\min\beta$ is
$\min(a+b+4c,\,3b+3c)$ for $a\ge b\ge c\ge 0$; for five levels it is $2b+2c$ (types $HHDHD$, Proposition 8.2 below); for
nine levels $4b+4c$ (exhaustive over the 15 isomorphism classes); for 11 and 13 levels sampling gives
$\min(2a+2b+6c,5b+5c)$ and $6b+6c$ (lower bounds only).

**Proposition 8.2 (five levels).** Rotational tournament on $\mathbb Z_5$, types $HHDHD$: $\alpha = (a+c, a+c, b+c,
a+c, 2b)$, $\beta = (b+c, b+c, 2a, b+c, a+c)$, so $\min\alpha = \min\beta = b+c$. (Direct count.)

**Proposition 8.3 (nine levels).** Rotational tournament on $\mathbb Z_9$ ($j\to j+1,\dots,j+4$), types $HHHHDHHHD$:
$$\alpha = (a+3c,\,a+3c,\,a+3c,\,a+3c,\,3b+c,\,a+3c,\,a+3c,\,a+3c,\,4b),\qquad
\beta = (b+3c,\,b+3c,\,b+3c,\,b+3c,\,4a,\,b+3c,\,b+3c,\,b+3c,\,3a+c),$$
so $\min\alpha = \min(a+3c,3b+c)$ and $\min\beta = b+3c$. (Direct count; also computed by layouts.py.)

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

- (Y0) $1\le K_{\mathcal B},K_{\mathcal A}\le\delta$ (complete bipartite graph);
- (Y1) $s+1\le\delta$ and $s^2+s+1\le K_{\mathcal B},K_{\mathcal A}\le(s^2+s+1)(\delta-s)$;
- (Y2) $s+1\le\delta$ and $N(s)\le K_{\mathcal B},K_{\mathcal A}\le N(s)+(s+1)(\delta-s-1)$;
- (Y3) $K_{\mathcal B} = K_{\mathcal A} = (2r'+1)N(s)$ with $s+1+r'\le\delta$.

*Proof.* (Y0): distances 2. (Y1): the incidence graph of $\mathrm{PG}(2,s)$ (points as $\mathcal B$, lines as
$\mathcal A$; diameter 3, same-colour distance 2) with pendant vertices: up to $\delta-s-1$ new $\mathcal B$-vertices
on each line and new $\mathcal A$-vertices on each point. A pendant $p$ on $c$ and a core vertex $x$ of the colour of
$p$: $c$ and $x$ have different colours, $d(c,x)\le 3$, so $d(p,x)\le 4$. Two pendants of one colour hang on core
vertices of one colour, at distance $\le 2$: $d\le 4$. (Y2): the incidence graph of $W(s)$ (same-colour distance
$\le 4$, fact (F1)) with up to $\delta-s-1$ pendant $\mathcal B$-vertices on each of the $s+1$ lines through a fixed point
$z_0$ and pendant $\mathcal A$-vertices on each of the $s+1$ points of a fixed line $m_0$: a pendant on a line $c$ and a
core point are within $1+3$; two pendants on lines through $z_0$ within $1+2+1$; dually. (Y3): the level graph of
Theorem A over $W(s)$ with $2r'+1$ levels has degree $s+1+r'$ and diameter 5, so same-colour distance $\le 4$. $\square$

Squad card c10 (research/squads/gqd5-r1/c10/table.md) tabulated the largest explicit balanced sizes (5, 15, 45, 120,
255, 468, 780, 1200, 2000, 2925, 4100 for $\delta = 2,\dots,12$; for $\delta = 3$ from (Y2), for $\delta\ge 4$ from (Y3), and
for $\delta = 2$ the 10-cycle, which is not in Lemma 9.1), and found that random
$\delta$-regular bipartite graphs satisfy the condition up to about 271 vertices per colour at $\delta = 8$.
Squad card r2c9 (research/squads/gqd5-r2/c9/construction.md, gen_hubs.py) extends (Y1), (Y2) by joining several
$\mathrm{PG}(2,s)$ cores: every balanced size $7\le K\le 48$ at $\delta = 6$ and $7\le K\le 153$ at $\delta = 8$ is
realised (some members found by a seeded search; each checked by BFS) (*Computer-checked*).
For the records we use a computer-found $Y$ (random degrees, then double-edge swaps that minimise the number of
same-colour hub pairs at distance $>4$ in $X_R^+$, paths through the levels counted; research/theorems/d5gq/hubopt.py),
and check the whole graph.

---

## 10. Families valid for every $q$

All ingredients below are explicit: the spread of Lemma 1.1 (an ovoid of $Q(4,q)$), the partial ovoid of Lemma 1.3,
the local dualities of Proposition 6.4, the hub graphs of Lemma 9.1, and for $q$ even a duality of $W(q)$.

**Corollary 10.1 ($q$ even, $1\le r\le q-1$).** Let all levels have type $H$ over $W(q)$, $M_t = \varphi|_P$ for the
duality $\varphi$ of Lemma 1.4, and $R_t = O_W$ the ovoid of Lemma 1.4 on every arc. Then for any $K_{\mathcal B},K_{\mathcal A}\le
r(q^2+1)$ for which an $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};q-r)$ exists (Lemma 9.1),
$$n_b(q+1+r,5)\ \ge\ (2r+1)\cdot 2N(q)+K_{\mathcal A}+K_{\mathcal B}.$$
*Proof.* Theorem B repairs every transition; Theorem 3.5 with $Y$ the hub graph. $\square$

**Corollary 10.2 ($q$ odd, $q\ge 5$, five levels).** Types $HHDHD$ over $Q(4,q)$ (Proposition 8.2) with the ovoid $O$ on $H\to
D$, the lines of $Q(4,q)$ corresponding to the points of Lemma 1.3 on $D\to H$ ($b = 3q-1$, $q\ge 5$), Proposition 6.4
on the non-friendly arcs: for $K_{\mathcal A},K_{\mathcal B}\le 3q+1$ with an $\mathrm{HG}_5(K_{\mathcal B},
K_{\mathcal A};q-2)$,
$$n_b(q+3,5)\ \ge\ 10N(q)+K_{\mathcal A}+K_{\mathcal B}.$$

**Corollary 10.3 ($q$ odd, $q\ge 5$, seven levels).** Types $HHHDHHD$ (Proposition 8.1), same ingredients: for
$K_{\mathcal B}\le 6q$ (the slot count gives
$\min(q^2+5,6q)$, which is $6q$ for $q\ge 5$), $K_{\mathcal A}\le 3q+3$ with an $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};q-3)$,
$$n_b(q+4,5)\ \ge\ 14N(q)+K_{\mathcal A}+K_{\mathcal B}.$$

**Corollary 10.4 ($q$ odd, $q\ge 5$, nine levels).** Types $HHHHDHHHD$ (Proposition 8.3), same ingredients: for
$K_{\mathcal B}\le\min(q^2+7,\,9q-1)$, $K_{\mathcal A}\le 3q+5$ with an $\mathrm{HG}_5(K_{\mathcal B},K_{\mathcal A};q-4)$,
$$n_b(q+5,5)\ \ge\ 18N(q)+K_{\mathcal A}+K_{\mathcal B}.$$

*Proofs.* Theorems B (friendly arcs: the ovoid is a partial ovoid, the set of Lemma 1.3 gives a partial spread of
$Q(4,q)$) and C/Proposition 6.4 (non-friendly arcs; on the $D\to D$ arc, where $M$ maps lines to points, the dual
statement of Proposition 6.4, for non-concurrent lines $x,y$ and non-collinear points $\ell,m$, which has the same proof)
repair every transition; slot counts from Propositions 8.1–8.3
with $a = q^2+1$, $b = 3q-1$, $c = 2$; Theorem 3.5. $\square$

**10.3 With computer-found sets.** Replacing $b$ by the size of a computer-found partial ovoid of $W(q)$ (Lemma 1.2(d)
bounds it by $q^2-q+1$) or a relaxed set (§7), and the hub graph by a computer-found one, gives the larger values of
§14. The best partial ovoids of $W(q)$ we found: 18 ($q=5$), 33 ($q=7$), 51 ($q=9$; four ILS runs and a group-orbit
search all stop at 50–51), 70 ($q=11$; tabu search; 68 from unions of orbits).

---

## 11. A $(13,5)$ graph on 11,636 vertices

**Computer-checked 11.1.** $n_b(13,5)\ge 11{,}636$.

*Construction* ($q = 9$, $r = 3$; built by research/theorems/d5gq/wgr.py with no extra freed points, i.e. the layout of
build_relaxed.py; solution file research/theorems/d5gq/graphs/d13D5_q9_relaxed66_n11636.json, edges
...n11636.edges.gz).

- $G = Q(4,9)$ as `W(9).dual()` (§1.2); levels $\mathbb Z_7$, rotational tournament, types $HHHDHHD$.
- $H\to D$ arcs ($0\to3$, $1\to3$, $2\to3$, $4\to6$, $5\to6$): $M = \mathrm{id}$, $R = O$, the ovoid of Lemma 1.1
  (82 points).
- $D\to H$ arcs ($3\to4$, $3\to5$, $6\to0$, $6\to1$, $6\to2$): $M = \mathrm{id}$, $R = T$, a relaxed set of 66 lines
  with 30 partner pairs (§7), listed in the solution file (`T`; also graphs/W9_relaxed_set_66.json as points of $W(9)$;
  found by squad card r2c1).
- The eleven non-friendly arcs ($0\to1$, $0\to2$, $1\to2$, $1\to4$, $2\to4$, $2\to5$, $4\to5$, $4\to0$, $5\to0$,
  $5\to1$ of type $H\to H$, and $3\to6$ of type $D\to D$): $M$ = the local duality of Proposition 6.4 on a
  two-element freed set, given in full in the solution file (`nonfriendly`).
- Slots: $\alpha = (86,86,86,134,86,86,198)$, $\beta = (70,70,70,246,70,70,166)$; $K_{\mathcal B} = 86$,
  $K_{\mathcal A} = 70$ hubs; the slot of every hub in every level is listed (`Bhub_slots`, `Ahub_slots`, as triples
  (level, element, arc)). The hub rule of Proposition 7.2 holds at all $5\cdot 60 = 300$ (arc, partnered line)
  instances (research/theorems/d5gq/check_rule.py).
- $Y$: 420 edges (`Y`), maximum degree 5 on the $\mathcal B$-side and $6 = q-r$ on the $\mathcal A$-side.

Every two vertices in different levels are within distance 5: by Theorems B and C for the $H\to D$ and the non-friendly
arcs, and by Propositions 7.1 and 7.2 for the $D\to H$ arcs; (HG) holds (checked over the whole graph by the builder);
so Theorem 3.6 gives order $7\cdot 2\cdot 820+86+70 = 11{,}636$, maximum degree $13$. **Computer-checked**:
research/lifts/coordinator_check/apsp.c (BFS from every vertex) reports bipartite, degree max 13, diameter 5
(graphs/d13D5_q9_relaxed66_n11636.check.txt). The neighbourhood of every vertex is determined by the solution file
through Definitions 2.1 and 3.1. The solution file also lists the 820 points of $\mathrm{PG}(3,9)$ and the 820 lines of
$W(9)$ explicitly; research/theorems/d5gq/sol2edges.py re-checks that they form $W(9)$, rebuilds the graph from the file
alone (without the builder's code) and finds exactly the same edge set.

Earlier versions: 11,605 and 11,621 with a 51-point partial ovoid instead of the relaxed set (without and with the
local dualities; graphs/d13D5_q9_typed_n11621.json); 11,626 and 11,627 with relaxed sets of 56 and 57 lines and at most
14 pairs, built with the stronger hub rule (graphs/d13D5_q9_relaxed_n11627.json).

---

## 12. Routing through a third level (computer experiments)

Theorem E is about two levels. With $2r+1\ge 5$ levels a pair $(u,j),(v,j')$ can also be joined through a third level
$i$ with two matching edges, e.g. $(x,j)\to(M_{j\to i}(x),i)\to(z,i)\to(M_{i\to j'}(z),j')\to(v,j')$ (length 4).
*Computer-checked* (squad cards):

- c19: seven levels over $Q(4,5)$, all type $H$: a **random** 16-point freed set on one non-friendly arc, violating
  (E2) and (E3), becomes harmless after annealing the other 20 matchings (apsp VALID, 2,184 vertices); five levels:
  8 points.
- c6: three levels over $Q(4,3)$: 5 freed points per transition with hubs (10 hubs, valid), all violating (E2) or (E3).
- r2c5: the typed seven-level layout of Proposition 8.1 over $Q(4,5)$ with $c$ freed points on **every** $H\to H$ arc,
  hubs included, annealing matchings, hub slots and $Y$: valid for $c = 2,3,4,5$ (2,236, 2,240, 2,244, 2,248 vertices;
  research/squads/gqd5-r2/c5/).
- r2c6: seven levels over $Q(4,7)$, no hubs: 16 freed points on one arc, 8 on each of two arcs, 4 on each of four arcs
  (all valid).
- The director's annealer research/theorems/d5gq/wgr.py (targeted swaps in the non-friendly matchings and moves of
  hub slots; bad pairs counted by wgr_eval.c on the whole graph with hubs but without $Y$, which is chosen at the end):
  at $q = 5$ it reaches zero bad pairs with 4 freed points per $H\to H$ arc (the hub graph then fails (HG) because
  $q-r = 2$). At $q = 9$, on top of the 11,636 graph of §11 with one extra freed point on each of the ten $H\to H$ arcs
  (which would give 11,640), three runs went from about 2,650 bad pairs to 10–16 in 200,000–250,000 swaps and then
  stalled; a greedy polish with 150 candidate moves per step did not close the last ones. (A first version also allowed
  swaps in the $D\to D$ arc $3\to6$. Routes between levels 3 and 6 through *one* other level use only friendly arcs and
  cannot repair those pairs. Routes through *two* other levels repair some of them (about 15% in the referee's test on
  the 11,636 graph, research/referee/d5_checks/arc36.py), but not enough, so the later runs keep that arc fixed.)

*Heuristic* (why this does not scale to $q = 11$): for a freed $x$ and a uniformly random $M$, a fraction
$(1-(q+1)/N)^{q(q+1)}$ of the elements of the other level violate (E2) (0.31, 0.32, 0.33, 0.34 for $q = 5,7,9,11$; about
$1/e$ for large $q$). A third level supplies about $(q+1)^2$ length-4 routes per freed element and per route type, so the
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
- $AS(q)$ at $\Delta = q+2$, in the model "copies of the incidence graph of $AS(q)$ plus line-to-line edges, no other
  vertices": points have degree $q+2$ and lines degree $q$, so only lines have spare edges (two each),
  and line-to-line edges must join copies of opposite types. From a point $p$ of one copy, a point of another copy of the
  same type is at even distance, and a path of length 4 to it must be $p$, a line through $p$, a line of a copy of the
  other type, a line of the target copy, a point on it; so $p$ reaches at most $2(q+2)q$ such points, fewer than the
  $q^3$ points of one copy when $q\ge 5$ (*Theorem*, by this count). Hence for $q\ge 5$ at most one copy of each type
  can be used, and the order stays $\le 4q^2(q+1)$.
We found no construction from a quadrangle of unequal order that approaches the lab's values at $\Delta\le 9$.

---

## 14. Comparison with the 2013 table and the lab's values

"Theorem family" = Corollaries 10.1–10.4 (explicit sets and hub graphs; research/theorems/d5gq/family_table.py,
family_table_out.txt); each of these six values was also built and checked by all-pairs BFS with independent scripts
(research/theorems/d5gq/family_check.py, family_check_even.py, written by the referee agent; output
family_check_out.txt). "Computer" = the best graph of §§8–11 type that we built and checked by all-pairs BFS. "Lab" =
the lab's value on 28 October 2026 (README, research/RESULTS.md). The $\Delta\le 9$ values of the table are Loz's
voltage lifts [Wiki] and the cells $(10,5)$–$(16,5)$ are credited to [DGQ] (§16).

| cell | table (2013) | theorem family | computer (this note) | lab | construction of the lab value |
|---|---:|---:|---:|---:|---|
| (10,5) | 4,000 | 4,044 ($q=7$, $r=2$) | 4,062 ($q=7$, $r=2$) | **4,800** | doubled-matching lift of $W(7)$ |
| (11,5) | 5,850 | 6,090 ($q=8$, $r=2$) | — | **7,020** | doubled-matching lift of $W(8)$ |
| (12,5) | 8,200 | 8,430 ($q=8$, $r=3$) | — | **9,840** | doubled-matching lift of $W(9)$ |
| (13,5) | 11,480 | 11,552 ($q=9$, $r=3$) | 11,636 ($q=9$, $r=3$) | **11,700** | multi-doubled-matching lift of $W(8)$ |
| (14,5) | 14,760 | 14,812 ($q=9$, $r=4$) | — | **17,568** | doubled-matching lift of $W(11)$ |
| (15,5) | 20,496 | 20,598 ($q=11$, $r=3$) | 20,715 ($q=11$, $r=3$) | **20,736** | route-chart lift |
| (16,5) | 27,300 | 26,453 ($q=11$, $r=4$) | — | **33,792** | route-chart lift |

At $\Delta\le 9$ (cells $(5,5)$–$(9,5)$) the level graphs have $6N(q)$ or $10N(q)$ vertices for small $q$ (e.g.
$(9,5)$: $6N(7) = 2{,}400$, $(7,5)$: $6N(5) = 936$) and the hubs add only $O(q)$; they are below the 2013 table there,
and far below the lab's values.

**Proposition 14.1 (ceilings of the construction).** Suppose every freed set on a friendly arc has at most
$B(q) = \lfloor 2(q+1)(q^2+1)/(2q+1)\rfloor$ elements, every freed set on a non-friendly arc at most $c$, and hubs are
as in Definition 3.1. Then the order is at most $(2r+1)\cdot 2N(q)+K$ with
$K = 2r\max(B(q),c)$ for any layout, and for $q$ odd $K = 2b+2c$, $\min(a+b+4c,3b+3c)$, $4b+4c$ with five, seven,
nine levels ($a,b\le B(q)$; $a\le q^2+1$ when $M = \mathrm{id}$ on the $H\to D$ arcs, by Theorem B). With $c = 2$
(Corollary 6.2) the best ceilings per cell are (research/theorems/d5relax/ceilings.py):

| cell | lab | ceiling | from |
|---|---:|---:|---|
| (10,5) | 4,800 | 4,110 | $q=7$, five levels |
| (11,5) | 7,020 | 6,122 | $q=8$, five levels |
| (12,5) | 9,840 | 8,598 | $q=8$, seven levels |
| (13,5) | 11,700 | 11,660 | $q=9$, seven levels (11,656 with $a = q^2+1$) |
| (14,5) | 17,568 | 15,112 | $q=9$, nine levels |
| (15,5) | 20,736 | 20,758 | $q=11$, seven levels (20,753 with $a = q^2+1$) |
| (16,5) | 33,792 | 26,868 | $q=11$, nine levels |
| (17,5) | — | 33,680 | $q=13$, seven levels; below $n_b(16,5)\ge 33{,}792$ |

*Proof.* $B(q)$ bounds partial ovoids, partial spreads and relaxed sets of points or of lines (the count of §7). Every
hub takes one slot in every level, so $K_{\mathcal B}\le\min_j\alpha_j$ and $K_{\mathcal A}\le\min_j\beta_j$; as
$\sum_j\alpha_j = \sum_j\beta_j = \sum_t|R_t|$ over the $r(2r+1)$ arcs, $K_{\mathcal A}+K_{\mathcal B}\le
2\sum_t|R_t|/(2r+1)\le 2r\max_t|R_t|$. For five, seven and nine levels, §8 gives the best layouts. $\square$

So (10,5)–(14,5) and (16,5) are out of reach of these constructions whatever relaxed sets exist; (13,5) would need at
least 13 freed elements on every non-friendly arc (each one adds 4 vertices), far beyond the two of Corollary 6.2.
Only (15,5) is open: with $a = q^2+1 = 122$ and $c = 2$ the order is $20{,}626+b$ (for $b\ge 62$), so $20{,}737$ needs
a relaxed set of $W(11)$ with $b\ge 111$ points. For partial ovoids this is exactly Tallini's bound $q^2-q+1$ (best
found: 70). Relaxed sets are not limited by Tallini's theorem, and since Lemma 7.3 their pairs may lie on any line;
but the best we found has 89 points (§7), which gives the 20,715 graph of Computer-checked 7.4. *Heuristic*: the
searches of §7 plateau at 89 from unrelated starts, and exact re-optimisation of large regions does not pass it, so we
expect the maximum to be near 90, well below 111. The other ways up are more freed elements per non-friendly arc (8 per
$H\to H$ arc with $b = 89$; third-level routing, §12, did not work beyond 2 at $q\ge 9$) or relaxed *point* sets on the
$H\to D$ arcs larger than the ovoid ($a+b\ge 233$), which the searches of §7 did not find.

---

## 15. Computer checks

All graphs were checked with research/lifts/coordinator_check/apsp.c (all-pairs bit-parallel BFS, no symmetry): simple,
bipartite, maximum degree, exact diameter.

| graph | file (research/theorems/d5gq/) | result |
|---|---|---|
| $(13,5)$, $n = 11{,}636$ | graphs/d13D5_q9_relaxed66_n11636.* | VALID, degree 13, diameter 5; independent rebuild (sol2edges.py) gives the same edges; hub rule checked (check_rule.py) |
| $(13,5)$, $n = 11{,}627$ | graphs/d13D5_q9_relaxed_n11627.* | VALID; independent rebuild identical |
| $(13,5)$, $n = 11{,}621$ | graphs/d13D5_q9_typed_n11621.* (json; rebuild with build_typed.py) | VALID |
| $(15,5)$-type, $q = 11$, $n = 20{,}715$, 4 pairs meeting at ovoid points | research/theorems/d5relax/graphs/d15D5type_q11_zo89.* (build_zo.py) | VALID (apsp_mt); independent rebuilds (sol2edges.py, referee's rebuild_record.py) identical; rule broken for one pair: diameter 6 |
| $(15,5)$-type, $q = 11$, $n = 20{,}713$ | graphs/d15D5type_q11_relaxed87_n20713.json (relaxed set of 87 lines; rebuild with sol2edges.py) | VALID (beats the table, not the lab) |
| $(15,5)$-type, $q = 11$, $n = 20{,}696$ | build_typed.py 11 3 HHHDHHD with the 70-point set | VALID |
| $(10,5)$-type, $q = 7$, $r = 2$, $n = 4{,}062$ | build_typed.py 7 2 HHDHD | VALID |
| $(8,5)$-type, $q = 5$, $r = 2$, $n = 1{,}596$ and $1{,}600$ | build_typed.py 5 2 HHDHD (and card c7 independently) | VALID |
| $(8,5)$-type, $q = 5$, relaxed line sets, $n = 1{,}610$ | squad card r2c7 (research/squads/gqd5-r2/c7/ld23.edges) | VALID; without the hub rule diameter 6 |
| relaxed sets, A-hub rule only, $q = 5, 7$, $n = 1{,}610$ and $4{,}086$ | squad card r3c4 (research/squads/gqd5-r3/c4/) | VALID; rule broken for one line: diameter 6 |
| explicit families (Cor. 10.1–10.4): $(10,5)$ 4,044, $(11,5)$ 6,090, $(12,5)$ 8,430, $(13,5)$ 11,552, $(14,5)$ 14,812, $(15,5)$ 20,598 | family_check.py, family_check_even.py (family_check_out.txt) | all VALID |
| 32 level graphs, $q\le 5$ | test_basic.py | all diameter 5 (Theorem A) |
| Theorem E vs brute force | test_basic.py | agree on 720 transitions |
| triads | triads.py | 0/2 in $Q(4,q)$, 1/$(q+1)$ in $W(q)$, $q = 3,5,7$ |
| local dualities | localdual.py | repaired, $q = 3,5$ |
| duality of $W(q)$, $q = 2,4,8$ | squad card c11 (research/squads/gqd5-r1/c11/) | verified; all-$H$ $q = 4$, $r = 1$: 544 VALID |

---

## 16. Prior art

- **The base graphs.** The CombinatoricsWiki table [Wiki] (read through the Internet Archive, snapshot of 14 January
  2025; table "as of January 2012", equal to [MS13, Table 4]) credits all seven cells $(10,5)$–$(16,5)$ to Delorme, Gómez
  and Quisquater [DGQ]; we could not find that paper. The orders of $(10,5)$–$(15,5)$ are those of the level graphs of
  Theorem A; $(16,5) = 27{,}300$ is not of this form (the level graphs give at most $26{,}352$ there), so [DGQ] contains
  more than these level graphs, and we can only say that the orders coincide, not that these are their graphs. The
  $D = 5$ cells with $\Delta = 5,\dots,9$ are Loz's voltage lifts from the project of Loz, Pérez-Rosés and
  Pineda-Villavicencio [Wiki] ($(4,5)$ is Hafner's and Loz's). The survey [MS13] gives no per-cell credit; it attributes
  the older bipartite constructions to Delorme and his collaborators (bipartite versions of the $*$-product and of
  compounding), and in its §3.3 describes the compounding of complete graphs into a bipartite Moore graph of diameter 6
  by Gómez, Miller, Pérez-Rosés and Pineda-Villavicencio (Networks 53 (2009)): general graphs and hexagons, related to
  the compounding here but not the same. We have not read Delorme–Gómez, *Some new large compound graphs*, European J.
  Combin. 23 (2002) 539–547, which the wiki lists among its references; it should be checked before the note is sent.
  Compounds of a bipartite graph with a tournament go back to Gómez and Fiol [GF85]. Delorme [De85] §3 builds
  cyclic multi-level graphs from a duality of a quadrangle, and §7–8 duplicates sets of vertices of a quadrangle's
  incidence graph (an ovoid/spread copy at $D = 4$). We claim none of these.
- **Hubs and deleted matching edges.** R. Rajiv (Zenodo, 30 Sept 2026, doi 10.5281/zenodo.23052995) deletes the edges
  of a type-preserving matching at a set of pairwise non-collinear points of a compound of generalized-polygon incidence
  graphs and attaches new vertices joined by a graph of diameter $\le n$, for general (non-bipartite) graphs of diameter
  $n = 4, 6$. Our friendly transitions with Theorem B are the bipartite, diameter $n+1$ version of that step, and our
  hubs are one-sided. The lab's literature check (research/lit/novelty-2026-10-25.md, branch
  claude/novelty-literature-check-4i5frp), done for the hexagon case, found nothing on local dualities or on relaxed
  freed sets with hub conditions. We did not search the literature for an exact criterion like Theorem E, for the
  converse in Theorem B, or for Corollary 6.2.
- **The lab's other $D = 5$ work.** The doubled-matching lifts of $W(q)$ (research/d10D7/DM_D5.md) give $12N(q)$ at
  degree $q+3$ and are better than everything here for $\Delta = 10, 11, 12, 14$. The lab's $(13,5)$ value is 11,700
  (recorded 26 Oct 2026, 09:44 PT, research/RESULTS.md), a multi-doubled-matching lift of $W(8)$ over
  $\mathbb Z_2\times\mathbb Z_5$ found by annealing (branch claude/new-cells-beyond-etos3t, research/frontier/beyond/MDM.md,
  graphs/d13D5_n11700_W8_2dm_Z10.edges.gz); before it, 11,486 $= 7\cdot 2N(9)+6$ (research/cell147/).
- **Finite geometry used.** Payne–Thas [PT] for all facts on quadrangles; Tallini [Ta91] for partial ovoids of $W(q)$,
  $q$ odd; Ceria–De Beule–Pavese–Smaldore [CDPS] for large partial ovoids of $W(3,q)$. The explicit family of Lemma 1.3
  was found by squad card r2c10; we did not find it in these sources.

**References.**
[CDPS] M. Ceria, J. De Beule, F. Pavese, V. Smaldore, *On large partial ovoids of symplectic and Hermitian polar spaces*,
J. Combin. Des. 31 (2023) 5–22, arXiv:2203.04553.
[De85] C. Delorme, *Grands graphes de degré et diamètre donnés*, European J. Combin. 6 (1985) 291–302.
[DGQ] C. Delorme, J. Gómez, J. J. Quisquater, *On large bipartite graphs*, submitted (cited by [Wiki]; not found).
[GF85] J. Gómez, M. A. Fiol, *Dense compound graphs*, Ars Combin. 20-A (1985) 211–237.
[MS13] M. Miller, J. Širáň, *Moore graphs and beyond: a survey of the degree/diameter problem*, Electron. J. Combin.
DS14v2 (2013).
[Wiki] E. Loz, H. Pérez-Rosés, G. Pineda-Villavicencio, *The degree-diameter problem for bipartite graphs*,
CombinatoricsWiki (2010); table "as of January 2012", read through the Internet Archive (snapshot of 14 January 2025).
[PT] S. E. Payne, J. A. Thas, *Finite Generalized Quadrangles*, 2nd ed., EMS, 2009.
[Ta91] G. Tallini, *Blocking sets with respect to planes in PG(3,q) and maximal spreads of a nonsingular quadric in
PG(4,q)*, Mitt. Math. Sem. Giessen 201 (1991) 141–147.
