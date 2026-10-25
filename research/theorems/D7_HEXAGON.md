# Bipartite graphs of diameter 7 from the split Cayley hexagon: level covers, surgery and hubs

Draft of 25 October 2026, written for Ignacio López and Gabriela Araujo-Pardo by the degree–diameter lab
(github.com/dogaozden/degree-diameter; Claude Code sessions coordinated by Doğa Özden). Job "thm-d7".

This note states and proves the constructions behind the lab's new lower bounds for the bipartite degree–diameter problem
at diameter 7 (cells (7,7), (9,7)–(16,7)). Everything below is meant to be checkable by hand: the geometric hypotheses are
stated in the language of the hexagon, and the neighbourhood of every vertex of every graph is given explicitly
(Definitions 2.1 and 3.1). Where a step depends on a computer search (the specific large sets and the auxiliary "hub
graphs" behind the record values), we say so and give the check. Section 10 lists the computer tests of every theorem on
small $q$.

**One correction to the lab notes.** The "relaxed friendly sets" of the lab notes (research/d15D7b/RELAXED.md) carry two
hypotheses, (R1) and (R2). Theorem C below shows that (R2), a condition on how the hub vertices are attached, is not
needed, and that (R1) can be weakened much further (to "segment sets", Definition 1.3). The records are unaffected (their
graphs satisfy the stronger hypotheses and were checked by computer in full), but the weaker hypothesis allows larger sets
than the ones used for the records (Remark 9.4).

## Contents

0. Results
1. The split Cayley hexagon: coordinates, distances, sets
2. Level covers (classical)
3. Surgery and hubs: the general assembly theorem
4. Theorem C: transitions that extend to an automorphism (friendly and duality transitions)
5. Theorem B: local dualities; mirrored sets
6. Typed level layouts and slot counts
7. Hub graphs
8. The record graphs as corollaries
9. What is proved for every $q$
10. Computer checks
11. Prior art, and what is new

---

## 0. Results

Notation: $n_b(\Delta, D)$ is the largest order of a bipartite graph with maximum degree $\le \Delta$ and diameter
$\le D$. For a prime power $q$ put
$$N = N(q) = \frac{q^6-1}{q-1} = (q+1)(q^4+q^2+1),$$
the number of points (and of lines) of a generalized hexagon of order $(q,q)$. The 2013 table (Miller–Širáň, dynamic survey
DS14v2) has, for $\Delta = q+1+r$, the value $(2r+1)\cdot 2N(q)$; this is the order of the level cover of Section 2.

| cell $(\Delta,7)$ | $q$, $r$ | table (2013) | ours | construction (this note) | parameters |
|-------|--------|---------:|----------:|----------------------------|---------------------------------|
| (7,7) | 5, 1 | 23,436 | **23,598** | 3 levels, one local duality (Cor. 8.1) | $\lvert R\rvert = 81$ (72 pairwise opposite + 9) |
| (9,7) | 7, 1 | 117,648 | **118,238** | same | $\lvert R\rvert = 295$ (288 + 7) |
| (10,7) | 8, 1 | 224,694 | **225,152** | same | $\lvert R\rvert = 229$ (217 + 12) |
| (11,7) | 9, 1 | 398,580 | **413,180** | 3 levels, duality, spread points freed (Cor. 8.2) | $\lvert F\rvert = 7{,}300$ |
| (12,7) | 9, 2 | 664,300 | **693,500** | 5 levels, duality, spread points freed (Cor. 8.2) | $\lvert F\rvert = 7{,}300$, $14{,}600 + 14{,}600$ hubs |
| (13,7) | 11, 1 | 1,062,936 | **1,064,472** | 3 levels, one local duality (Cor. 8.1) | $\lvert R\rvert = 768$ (756 + 12) |
| (14,7) | 11, 2 | 1,771,560 | **1,789,588** | typed levels HDHDH + local duality (Cor. 8.3) | 8,645 pts / 8,246 lines / 768; $9{,}014 + 9{,}014$ hubs |
| (15,7) | 11, 3 | 2,480,184 | **2,501,491** | typed levels HHDHDHD + local duality (Cor. 8.3) | twelve segment sets, 768; $10{,}826 + 10{,}481$ hubs |
| (16,7) | 13, 2 | 4,022,340 | **4,052,108** | typed levels HDHDH + pairwise opposite sets (Cor. 8.3) | 14,762 pts / 14,823 lines / 122; $14{,}884 + 14{,}884$ hubs |

All nine graphs were rebuilt by the lab's coordinator from their solution files and checked by a breadth-first search from
every vertex (no symmetry assumed): bipartite, maximum degree $\Delta$, diameter 7 (logs in research/coordinator_check/,
Section 10). The cell (8,7) record is a Haar graph and is not discussed here.

The theorems are:

- **Theorem A** (classical): the level cover with $2r+1$ levels and arbitrary matchings has diameter $\le 7$.
- **Lemma 3.3 and Theorem 3.4** (assembly): if every "transition" survives the deletion of its freed matching edges with
  all its pairs still within distance 7, then hub vertices can be attached to the freed slots in any way, and the result
  has diameter 7 as soon as hubs of the same colour are within distance 6.
- **Theorem C**: a transition whose matching is the restriction of an automorphism of the incidence graph (the identity
  between $H$ and its dual, or a duality of $H$) survives the deletion at any *segment set*: a point set in which every
  point is collinear with other points of the set along at most one line. Such sets have at most $(q+1)(q^3+1)$
  points, with equality exactly for the point sets of spreads.
- **Theorem B**: a transition with an arbitrary matching $M$ survives the deletion at a non-collinear point set $R$ if
  $M(R)$ is non-concurrent and $M$ maps the points collinear with $x$ onto the lines concurrent with $M(x)$, for every
  $x\in R$. Propositions 5.1 and 5.2 say when such an $M$ exists ("mirrored sets").

---

## 1. The split Cayley hexagon

### 1.1 Coordinates

Let $q$ be a prime power and $V = \mathbb F_q^7$ with coordinates $(X_0,\dots,X_6)$. Let
$$Q(X) = X_0X_4 + X_1X_5 + X_2X_6 - X_3^2,$$
with polar form $B(X,Y) = Q(X+Y)-Q(X)-Q(Y) = X_0Y_4+X_4Y_0+X_1Y_5+X_5Y_1+X_2Y_6+X_6Y_2-2X_3Y_3$ (alternating when $q$ is
even). The parabolic quadric $Q(6,q)$ is the set of points $\langle x\rangle$ of $\mathrm{PG}(6,q)$ with $Q(x)=0$. It is
convenient to write $x = (v, a, w)$ with $v = (x_0,x_1,x_2)$, $a = x_3$, $w = (x_4,x_5,x_6)$; then $Q(x) = v\cdot w - a^2$.

The **split Cayley hexagon** $H = H(q)$ (Tits 1959; see [VM98, §2.4]) has

- **points**: the set $P$ of all $N = (q^6-1)/(q-1)$ points of $Q(6,q)$;
- **lines**: the set $L$ of the lines of $Q(6,q)$ whose Grassmann coordinates $p_{ij} = x_iy_j - x_jy_i$ (for any two spanning points
  $x, y$) satisfy Tits' equations, which for this quadric we write as
  $$p_{12} = p_{34},\quad p_{54} = p_{32},\quad p_{20} = p_{35},\quad p_{65} = p_{30},\quad p_{01} = p_{36},\quad p_{46} = p_{31};$$
- **incidence**: containment.

(Labellings of the coordinates differ between sources; this is the form used by all the lab's generators. We checked by
computer, from scratch, that with this quadric it gives a generalized hexagon of order $(q,q)$ for $q = 2, 3, 4, 5$: right
numbers of points and lines, $q+1$ on each, incidence graph of diameter 6 and girth 12, Section 10.1. A variant with
$p_{20} = p_{36}$ and $p_{01} = p_{35}$, which we had first quoted from memory, does not give a generalized hexagon.)

*Example.* For $x = e_0 = (1,0,\dots,0)$ and a point $y$, $p_{0j} = y_j$ and $p_{ij} = 0$ for $i,j\ge 1$; the equations
reduce to $y_1 = y_2 = y_3 = 0$, and $B(e_0,y) = y_4 = 0$. So the $q+1$ lines through $e_0$ are
$\langle e_0, \lambda e_5+\mu e_6\rangle$, $(\lambda:\mu)\in\mathrm{PG}(1,q)$: they lie in the totally singular plane
$\langle e_0, e_5, e_6\rangle$. (In general the lines of $H(q)$ through a point $x$ are the lines through $x$ of a
totally singular plane $\pi_x\subset x^\perp$.)

$H(q)$ is a generalized hexagon of order $(q,q)$: $N$ points and $N$ lines, $q+1$ points on a line and $q+1$ lines on a
point. The group $G_2(q)$ acts on it; for instance $g\in SL(3,q)$ acts by $(v,a,w)\mapsto (gv, a, g^{-T}w)$ (this is the
symmetry used to check the (16,7) graph, research/squads/cells/d16D7.md).

The **dual hexagon** $H^D$ has the lines of $H$ as points and the points of $H$ as lines. A **duality** of $H$ is an
isomorphism $H\to H^D$, i.e. a bijection $\varphi$ of $P\cup L$ with $\varphi(P) = L$, $\varphi(L) = P$, preserving
incidence. $H(q)$ has a duality if and only if $q = 3^h$ (Tits 1959; [VM98, Ch. 3]). For $q = 9$ we use an explicit
duality found by computer (research/d10D7/dual/dualfind.c: it extends a polarity of the subhexagon $H(3)$ over
$\mathbb F_3\subset\mathbb F_9$ by propagation along geodesics and then checks that all $N(q+1)$ incidences are
preserved).

### 1.2 The incidence graph and distances

$I = I(q)$ denotes the incidence graph of $H$: vertex set $P\cup L$ ($2N$ vertices), $x\sim y$ when $x$ and $y$ are
incident. $d(x,y)$ is the distance in $I$, and $\Gamma_i(x) = \{y : d(x,y) = i\}$. Points are at even distance from
points, lines at odd distance from points. Two points are *collinear* when $d = 2$, two lines *concurrent* when $d = 2$,
and two elements are *opposite* when $d = 6$.

$\Gamma_2(x)$ for a point $x$ is the set of the $q(q+1)$ points collinear with $x$; for a line $\ell$ it is the set of the
$q(q+1)$ lines concurrent with $\ell$. The sizes are $\lvert\Gamma_i(x)\rvert = (q+1)q^{i-1}$ for $1\le i\le 5$ and
$\lvert\Gamma_6(x)\rvert = q^5$.

We use the following standard facts.

**(F1)** $I$ is connected, bipartite, $(q+1)$-regular, of diameter 6 and girth 12 (this is the definition of a
generalized hexagon of order $(q,q)$).

**(F2) Geodesics.** If $d(x,y)\le 5$ there is a unique geodesic from $x$ to $y$ (two would close a cycle of length
$\le 10$). If $d(x,y) = 6$, then every $z\in\Gamma_1(x)$ satisfies $d(z,y) = 5$ (it is odd, and at least $6-1$), so for
every neighbour $z$ of $x$ there is exactly one geodesic from $x$ to $y$ through $z$.

**(F3) Covering lemma.** Let $x, y$ be elements of $H$. There is $z\in\Gamma_2(x)$ with
$d(z,y)\le 3$ if $x$ and $y$ have different types, and $d(z,y)\le 4$ if they have the same type.
*Proof.* If $2\le d(x,y)\le 6$, take for $z$ the vertex at distance 2 from $x$ on a geodesic from $x$ to $y$:
$d(z,y) = d(x,y)-2$. If $d(x,y) = 1$, take $z\in\Gamma_1(y)\setminus\{x\}$ (then $z\in\Gamma_2(x)$ and $d(z,y) = 1$). If
$x = y$ any $z\in\Gamma_2(x)$ has $d(z,y) = 2$. The largest value is $6-2 = 4$ for the same type and $5-2 = 3$ for
different types. $\square$

**(F4) Orthogonality.** For points $x, y$ of $H(q)$: $d(x,y)\le 4$ if and only if $B(x,y) = 0$ (the points not opposite
$x$ are the points of $Q(6,q)$ in the tangent hyperplane $x^\perp$; [VM98, §2.4]; both sides count
$1+q+q^2+q^3+q^4$ points). We re-checked (F4) by computer for all pairs of points for $q = 2, 3, 4$ and for a sample of
points for $q = 5$ (Section 10.1); the lab's large computations (research/d13D7/REPORT.md §3) also rely on it.

### 1.3 Sets of points and lines

**Definition 1.1.** A set of points of $H$ is
- *non-collinear* if no two of its points are collinear (a partial distance-2 ovoid);
- a *partial ovoid* if its points are pairwise opposite; an *ovoid* if moreover it has $q^3+1$ points.

Dually, a set of lines is *non-concurrent*, a *partial spread* (pairwise opposite lines), or a *spread* ($q^3+1$
pairwise opposite lines).

By (F4), partial ovoids of $H(q)$ are exactly the sets of pairwise non-orthogonal points of $Q(6,q)$, i.e. partial ovoids
of the polar space $Q(6,q)$.

**Lemma 1.2 (standard examples).**
(a) If $\Sigma$ is a 3-space of $\mathrm{PG}(6,q)$ with $\Sigma\cap Q(6,q)$ an elliptic quadric $Q^-(3,q)$, its $q^2+1$
points form a partial ovoid of $H(q)$, for every $q$.
(b) (Hermitian spread [Th80].) If $\Pi$ is a hyperplane with $\Pi\cap Q(6,q)$ an elliptic quadric $Q^-(5,q)$, the lines of
$H(q)$ contained in $\Pi$ form a spread, for every $q$.
(c) If $S$ is a spread, every line not in $S$ meets exactly one line of $S$.
(d) If $q = 3^h$ and $\varphi$ is a duality, $\varphi(S)$ is an ovoid for every spread $S$.

*Proof.* (a) If $x\ne y$ are points of $Q^-(3,q)$ with $B(x,y) = 0$, then $Q(\lambda x+\mu y) = \lambda\mu B(x,y) = 0$, so
the line $xy$ lies in $Q^-(3,q)$, which contains no line. So $B(x,y)\ne 0$ and $x, y$ are opposite by (F4).
(b) is in [Th80]; we also checked it by computer for small $q$ (Section 10.1), and the record builders re-check, for the
sets they use, the hypotheses of the theorems they apply (Section 10.2).
(c) A line meeting two lines of $S$ would put them at distance $\le 4$. So the lines of $S$ together with the
$q(q+1)$ lines meeting each of them are $(q^3+1)(1+q(q+1)) = (q^3+1)(q^2+q+1) = N$ distinct lines, i.e. all lines. (d) $\varphi$ preserves distances. $\square$

Ovoids of $Q(6,q)$ (equivalently of $H(q)$) exist for $q = 3^h$; they do not exist for $q$ even [Th81] or for $q$ prime
$\ge 5$ [BGS06]. The largest partial ovoids are not known in general; the lab's record graphs use partial ovoids found by
computer (Section 8).

The following class of sets is the one that matters for Theorem C. It contains the non-collinear sets and the point
sets of partial spreads.

**Definition 1.3 (segment sets).** A set $F$ of points is a *segment set* if for every $p\in F$ the points of
$F\setminus\{p\}$ that are collinear with $p$ all lie on one line through $p$. Equivalently: there are no
$p, p', p''\in F$ with $d(p,p') = d(p',p'') = 2$ and $d(p,p'') = 4$ (a path of two collinearities that turns at $p'$).
Dually, a set $G$ of lines is a *dual segment set* if for every $\ell\in G$ the lines of $G\setminus\{\ell\}$ that meet
$\ell$ all pass through one point of $\ell$.

So a segment set is a disjoint union of "segments" (sets of $\ge 2$ points on a line) and isolated points, such that no
two points from different pieces are collinear. Examples:
- every non-collinear set;
- every set in which each point is collinear with at most one other point of the set (the "relaxed sets" (R1) of the lab
  notes);
- every subset of the point set of a partial spread (points on distinct lines of a partial spread are not collinear,
  since the lines are opposite);
- dually: the set of all lines through the points of a partial ovoid (lines through distinct points of a partial ovoid
  never meet).

**Proposition 1.4 (size of segment sets).** A segment set $F$ has $\lvert F\rvert\le (q+1)(q^3+1)$, with equality if and
only if $F$ is the point set of a spread. Dually, a dual segment set has at most $(q+1)(q^3+1)$ lines, with equality if
and only if it is the set of lines through the points of an ovoid.

*Proof.* Let $F_1$ be the points of $F$ collinear with no other point of $F$, and $C_1,\dots,C_m$ the segments (maximal
sets of $\ge 2$ points of $F$ on a line $s_i$; $\lvert C_i\rvert\le q+1$). A line meeting $F$ in exactly one point is
called a *private* line of that point. A point of $F_1$ has $q+1$ private lines and a point of a segment $C_i$ has $q$ (all
its lines except $s_i$, which contain no other point of $F$ by the segment property). Private lines of different points
are different, and different from the $s_i$. So
$$(q+1)\lvert F_1\rvert + q\sum_i \lvert C_i\rvert + m\ \le\ N .$$
Since $m\ge \sum_i\lvert C_i\rvert/(q+1)$, the left side is at least $(q + \tfrac1{q+1})\lvert F\rvert$, which gives
$\lvert F\rvert\le N(q+1)/(q^2+q+1) = (q+1)(q^3+1)$. Equality forces $F_1 = \emptyset$, $\lvert C_i\rvert = q+1$ (whole
lines) and $m = q^3+1$. The lines $s_i$ are then pairwise opposite: if $s_i$ and $s_k$ met in a point $z$, then $z\in F$
would have other points of $F$ on two lines; if $d(s_i,s_k) = 4$, a point of $s_i$ would be collinear (along the line
joining them) with a point of $s_k$, and would also have other points of $F$ on $s_i$. So they form a spread. Conversely the point set of a spread is a segment set of
this size. The dual statement is the same proof in $H^D$. $\square$

For comparison, a non-collinear set has at most $q^4+q^2+1$ points (Hoffman's ratio bound on the collinearity graph, whose
smallest eigenvalue is $-(q+1)$; equality would need a distance-2 ovoid, a point set meeting every line exactly once), and $(q+1)(q^3+1) = q^4+q^3+q+1$ is larger by $q^3-q^2+q$.

---

## 2. Level covers

Fix $r\ge 1$; there are $2r+1$ levels, indexed by $j\in\mathbb Z_{2r+1}$. Each level gets a **type**
$\tau_j\in\{H, D\}$. For a type $\tau$ let
$$A(H) = P,\quad B(H) = L,\qquad A(D) = L,\quad B(D) = P$$
(the "points" and "lines" of $H$ or of $H^D$). A **transition** is a pair $t = (j,k)$ with $j\in\mathbb Z_{2r+1}$,
$1\le k\le r$; its source level is $j$ and its target level is $j+k$. It is **friendly** if $\tau_j\ne\tau_{j+k}$; then
$A(\tau_j) = B(\tau_{j+k})$.

**Definition 2.1 (level cover).** Given types $\tau$ and, for every transition $t=(j,k)$, a bijection
$M_t: A(\tau_j)\to B(\tau_{j+k})$, the graph $X = X(\tau, M)$ has vertex set $(P\cup L)\times\mathbb Z_{2r+1}$ and edges
- $(x,j)\sim(y,j)$ whenever $x$ and $y$ are incident ("level edges");
- $(a,j)\sim(M_{(j,k)}(a), j+k)$ for every $j$, every $1\le k\le r$ and every $a\in A(\tau_j)$ ("matching edges").

Colour the vertices $(a,j)$, $a\in A(\tau_j)$, with colour $\mathcal A$ and the vertices $(b,j)$, $b\in B(\tau_j)$, with
colour $\mathcal B$. Level edges and matching edges join different colours, so $X$ is bipartite. The neighbourhoods are:
$$N(a,j) = \Gamma_1(a)\times\{j\}\ \cup\ \{(M_{(j,k)}(a), j+k) : 1\le k\le r\}\qquad (a\in A(\tau_j)),$$
$$N(b,j) = \Gamma_1(b)\times\{j\}\ \cup\ \{(M_{(j-k,k)}^{-1}(b), j-k) : 1\le k\le r\}\qquad (b\in B(\tau_j)).$$
So $X$ is $(q+1+r)$-regular of order $(2r+1)\cdot 2N$.

When all levels have type $H$ and all $M_t$ equal one bijection $\sigma: P\to L$, this is the graph whose order is the
table value (for $r=1$: three copies of $I$ joined by $(p,i)\sim(\sigma(p),i+1)$).

**Theorem A (level cover).** For all types and all bijections $M_t$, $X(\tau, M)$ has diameter at most 7. More
precisely: two vertices of one level are joined by a path of length $\le 6$ inside that level, and for every transition
$t=(j,k)$ every vertex of level $j$ is joined to every vertex of level $j+k$ by a path of length $\le 7$ that uses only
level edges of levels $j$ and $j+k$ and matching edges of $t$.

*Proof.* Inside a level this is (F1). Every two distinct levels differ by $\pm k$ for some $1\le k\le r$ (as
there are $2r+1$ levels), so it is enough to join $(u,j)$ to $(v,j')$, $j' = j+k$, with $M = M_{(j,k)}$:
1. $u\in A(\tau_j)$: $(u,j)\to(M(u),j')\leadsto(v,j')$, length $\le 1+6$.
2. $u\in B(\tau_j)$, $v\in B(\tau_{j'})$: with $a = M^{-1}(v)$, $(u,j)\leadsto(a,j)\to(v,j')$, length $\le 5+1$ (in $I$,
   elements of different types are at distance $\le 5$).
3. $u\in B(\tau_j)$, $v\in A(\tau_{j'})$: pick $b\in\Gamma_1(v)$ and $a = M^{-1}(b)$:
   $(u,j)\leadsto(a,j)\to(b,j')\to(v,j')$, length $\le 5+1+1$. $\square$

---

## 3. Surgery and hubs

### 3.1 The construction

**Definition 3.1 (surgery and hubs).** Start from a level cover $X(\tau, M)$ and choose for every transition $t=(j,k)$
a set $R_t\subseteq A(\tau_j)$ of **freed elements** (possibly empty).

1. *Deletion.* Delete the matching edges $(a,j)\sim(M_t(a),j+k)$, $a\in R_t$. Call the result $X_R$. Each deleted edge
   leaves a **free $\mathcal A$-slot** at $(a,j)$ and a **free $\mathcal B$-slot** at $(M_t(a), j+k)$. Level $j$ has
   $$\alpha_j = \sum_{k=1}^r \lvert R_{(j,k)}\rvert\ \text{ free }\mathcal A\text{-slots},\qquad
     \beta_j = \sum_{k=1}^r \lvert R_{(j-k,k)}\rvert\ \text{ free }\mathcal B\text{-slots}.$$
2. *Hubs.* Add $K_{\mathcal B}\le\min_j\alpha_j$ new vertices of colour $\mathcal B$ (**$\mathcal B$-hubs**) and
   $K_{\mathcal A}\le\min_j\beta_j$ new vertices of colour $\mathcal A$ (**$\mathcal A$-hubs**). Each $\mathcal B$-hub
   $h$ is joined to exactly one free $\mathcal A$-slot $s_j(h)$ in every level $j$, each $\mathcal A$-hub $g$ to exactly
   one free $\mathcal B$-slot $s'_j(g)$ in every level; every slot is used at most once. (The assignment is otherwise
   arbitrary; a hub may use slots of different freed elements in different levels.)
3. *Hub graph.* Add a bipartite graph $Y$ between the $\mathcal B$-hubs and the $\mathcal A$-hubs.

Call the result $X_R^+$. In the lab notes, $\mathcal B$-hubs are "line-side hubs" (in an $H$ level they are joined to
points) and $\mathcal A$-hubs "point-side hubs".

*Exact neighbourhoods.* For a level vertex, the neighbourhood is that of Definition 2.1 minus the deleted matching edges
plus one hub for each used free slot. For hubs:
$$N(h) = \{(s_j(h), j) : j\in\mathbb Z_{2r+1}\}\cup N_Y(h),\qquad N(g) = \{(s'_j(g), j): j\in\mathbb Z_{2r+1}\}\cup N_Y(g).$$

*Degree and order.* Level vertices have degree $\le q+1+r$ (equality when all their free slots are used), hubs have
degree $2r+1+\deg_Y$. So $X_R^+$ is bipartite with maximum degree $\le q+1+r$ as soon as $Y$ has maximum degree
$\le q-r$, and its order is
$$\lvert X_R^+\rvert = (2r+1)\cdot 2N + K_{\mathcal A} + K_{\mathcal B}.$$

### 3.2 Assembly

**Definition 3.2.** A transition $t=(j,k)$ is **repaired** (by $R_t$) if in $X_R$ every vertex of level $j$ is joined to
every vertex of level $j+k$ by a path of length $\le 7$ that uses only level edges of levels $j, j+k$ and the
remaining matching edges of $t$.

Whether $t$ is repaired depends only on $M_t$ and $R_t$ (not on the other transitions, and not on the hubs).

**Lemma 3.3 (hubs).** Let $X_R^+$ be as in Definition 3.1. Then
- every hub is within distance 7 of every level vertex;
- every $\mathcal B$-hub is within distance 7 of every $\mathcal A$-hub.

*Proof.* A $\mathcal B$-hub $h$ and a level vertex $(v,j)$: $h\to(s_j(h),j)\leadsto(v,j)$ inside level $j$, length
$\le 1+6$. The level copies are never touched by the surgery. A $\mathcal B$-hub $h$ and an $\mathcal A$-hub $g$: in
level $0$, $s_0(h)\in A(\tau_0)$ and $s'_0(g)\in B(\tau_0)$ have different types, so
$h\to(s_0(h),0)\leadsto(s'_0(g),0)\to g$ has length $\le 1+5+1$. $\square$

**Theorem 3.4 (assembly).** Suppose
- (T) every transition $t$ is repaired by $R_t$, and
- (HG) any two $\mathcal B$-hubs, and any two $\mathcal A$-hubs, are within distance 6 in $X_R^+$.

Then $X_R^+$ has diameter $\le 7$. If moreover $Y$ has maximum degree $\le q-r$, then
$$n_b(q+1+r,\,7)\ \ge\ (2r+1)\cdot 2N(q) + K_{\mathcal A} + K_{\mathcal B}.$$

*Proof.* Pairs of level vertices: same level by (F1), different levels by (T) (as in the proof of Theorem A, every pair of
levels is the pair of some transition). Pairs with a hub: Lemma 3.3 and (HG). $\square$

(HG) holds for instance when $Y$ alone has all same-colour distances $\le 6$; it can also use paths through the levels
(two $\mathcal B$-hubs whose slots in some level are at distance $\le 4$ are within distance 6). Section 7 discusses
hub graphs.

So everything reduces to geometric conditions under which one transition is repaired. Sections 4 and 5 give two.

---

## 4. Theorem C: transitions that extend to an automorphism

A transition $t = (j,k)$ is **automorphic** if $M_t$ is the restriction to $A(\tau_j)$ of an automorphism $\psi$ of
the graph $I$ with $\psi(A(\tau_j)) = B(\tau_{j+k})$. The two cases used here:
- a *friendly* transition with $M_t = \mathrm{id}$ ($\psi = \mathrm{id}$; $A(\tau_j) = B(\tau_{j+k})$);
- an $H\to H$ transition with $M_t = \varphi\vert_P$ for a duality $\varphi$ ($q = 3^h$); a $D\to D$ transition with
  $M_t = \varphi\vert_L$.

(A friendly transition whose matching is a collineation of $H$, restricted to points or to lines, is also automorphic.)

**Lemma 4.1.** Let $F$ be a segment set of points. For all elements $u, v$ of $H$ there is a point $p\notin F$ with
$$d(u,p) + d(p,v)\ \le\ 6 .$$

*Proof.* If some point $p$ on a geodesic from $u$ to $v$ is not in $F$, then $d(u,p)+d(p,v) = d(u,v)\le 6$. Assume
that all points on all geodesics from $u$ to $v$ lie in $F$.

A geodesic with three points $p, p', p''$ in a row ($p - m - p' - m' - p''$ with lines $m\ne m'$) cannot have all three
in $F$ (that is a turning path, excluded by Definition 1.3). A geodesic between two points at distance 4 or 6, a point
and a line at distance 5, or two lines at distance 6 contains three points in a row. So only the following cases remain;
in each we exhibit $p\notin F$ with $d(u,p)+d(p,v)\le 6$. We use repeatedly: *if $p_0\in F$ has a point of $F$ on the
line $s$ through it, then no point $p\ne p_0$ collinear with $p_0$ off $s$ is in $F$* (Definition 1.3).

(a) $u = v$ a point of $F$. Let $s$ be a line through $u$ containing every point of $F$ collinear with $u$ (any line if
there is none). Take a line $y\ne s$ through $u$ and $p\in y\setminus\{u\}$: $p\notin F$ and $d(u,p)+d(p,u) = 4$.

(b) $u, v$ collinear points of $F$ on the line $s$. Take $y\ne s$ through $u$ and $p\in y\setminus\{u\}$: $p\notin F$,
$d(u,p) = 2$, $d(p,v)\le 4$.

(c) $u\in F$ a point, $v$ a line through $u$. If $v$ has a point $p\ne u$ outside $F$: $2+1 = 3$. Otherwise all points
of $v$ are in $F$; take $y\ne v$ through $u$ and $p\in y\setminus\{u\}$: $p\notin F$, $d(u,p) = 2$,
$d(p,v)\le 3$.

(d) $u$ a point, $v$ a line, $d(u,v) = 3$, geodesic $u - s - p_2 - v$ with $u, p_2\in F$. A point $p\in v\setminus\{p_2\}$
has $d(u,p) = 4$, $d(p,v) = 1$. If all of them were in $F$, $p_2$ would have points of $F$ on the two lines $s$ and $v$.

(e) $u, v$ lines meeting in $p_1\in F$. Not both $u$ and $v$ contain a second point of $F$ (else $p_1$ turns). Say $u$
does not: take $p\in u\setminus\{p_1\}$, so $p\notin F$, $d(u,p) = 1$, $d(p,v) = 3$.

(f) $u, v$ lines at distance 4, geodesic $u - p_1 - y - p_3 - v$ with $p_1, p_3\in F$. Then no other point $p$ of $u$ is
in $F$ (else $p_1$ turns: $p$ on $u$, $p_3$ on $y$), and $d(u,p) = 1$, $d(p,v)\le d(p,p_1)+d(p_1,v) = 2+3$.

(g) $u = v$ a line. If some point of $u$ is not in $F$: $1+1$. Otherwise take $p_1\in u$, a line $y\ne u$ through $p_1$ and
$p\in y\setminus\{p_1\}$: $p\notin F$ and $d(u,p) = 3$, so $3+3 = 6$.

The cases with $u$ a line and $v$ a point are (c), (d) with $u$ and $v$ exchanged. $\square$

**Theorem C.** Let $t = (j,k)$ be an automorphic transition. If $A(\tau_j) = P$ and $R_t$ is a segment set of points, or
$A(\tau_j) = L$ and $R_t$ is a dual segment set of lines, then $t$ is repaired.

*Proof.* Let $\psi$ be the automorphism of $I$ extending $M = M_t$, $j' = j+k$, and take $(u,j)$, $(v,j')$. For every
$a\in A(\tau_j)\setminus R_t$ the path
$$(u,j)\leadsto(a,j)\to(\psi(a),j')\leadsto(v,j')$$
has length $d(u,a) + 1 + d(\psi(a),v) = d(u,a) + 1 + d(a,\psi^{-1}(v))$, since $\psi$ is an isometry of $I$. If
$A(\tau_j) = P$, Lemma 4.1 applied to $u$, $\psi^{-1}(v)$ and $F = R_t$ gives $a$ with $d(u,a)+d(a,\psi^{-1}(v))\le 6$,
so the path has length $\le 7$. If $A(\tau_j) = L$, apply Lemma 4.1 in $H^D$ (same graph $I$, points and lines
exchanged; a dual segment set of $H$ is a segment set of $H^D$). $\square$

**Remark 4.2 (sharpness, two levels).** Within the two levels $j, j+k$, the hypothesis cannot be weakened: if
$p, p', p''\in R_t$ turn at $p'$ ($p - m - p' - m' - p''$, $m\ne m'$), take a line $u\ne m'$ through $p''$. Then
$d(p,u) = 5$ with the unique geodesic $p - m - p' - m' - p'' - u$. A path from $(u,j)$ to $(\psi(p),j')$ inside the two
levels uses an odd number $2h+1$ of matching edges of $t$, and (transporting the segments in level $j'$ back by
$\psi^{-1}$ and using the triangle inequality) has length at least $2h+1+d(u,p) = 2h+6$. So a path of length $\le 7$ uses
one matching edge, at a point $a$ with $d(u,a)+d(a,p) = 5$, i.e. $a\in\{p, p', p''\}$: all three edges are deleted, and
the distance in the two levels is $> 7$. (In the whole graph, routes through a third level or through hubs might still
exist; in the lab's five-level graph over $H(9)$ with the 7,300 spread points freed and no hubs, freeing one more point
left 82,720 ordered pairs at distance $> 7$, research/squads/cells/d12D7.md §2.)

**Corollary 4.3.** The following transitions are repaired:
1. a friendly transition with $M_t = \mathrm{id}$ and $R_t$ a non-collinear set of points (if $\tau_j = H$) or a
   non-concurrent set of lines (if $\tau_j = D$) — the "one-transition theorem at friendly transitions" of the lab notes;
2. the same with $R_t$ a set in which every element has at most one partner (collinear, resp. concurrent element of
   $R_t$) — the relaxed sets (R1) of research/d15D7b/RELAXED.md, **without** its hub condition (R2);
3. an $H\to H$ transition with $M_t$ a duality and $R_t$ any subset of the points of a partial spread
   (research/squads/cells/d12D7.md §2; e.g. all $(q+1)(q^3+1)$ points of the Hermitian spread, $q=3^h$).

*Why the lab's (R2) was not needed.* The lab proof of the relaxed theorem (RELAXED.md, cases 4 and 5) only used paths
whose matching edge sits at a point collinear with the freed point $r$. When $r$ has a partner $x$ and the target is a
line $u$ with $d(r,u) = 5$ and geodesic $r - y - x - y_2 - w_2 - u$, the only such point is $x$ (freed), and (R2) supplies
a hub. The path through $w_2$ (at distance 4 from $r$) avoids this: $w_2$ is collinear with $x$, so it is not freed (else $x$
would have two partners), and $(r,j')\leadsto(w_2,j')\to(w_2,j)\to(u,j)$ has length $4+1+1 = 6$. This is case (d) of
Lemma 4.1.

---

## 5. Theorem B: local dualities

For transitions that are not automorphic (an $H\to H$ transition when $q\ne 3^h$, or any $H\to H$ transition whose
matching is not a duality) we only ask $M_t$ to behave like a duality near the freed elements.

**Theorem B (one-transition surgery).** Let $t = (j,k)$ be any transition, $M = M_t$, and $R = R_t\subseteq A(\tau_j)$.
Suppose
- (H1) no two elements of $R$ are at distance 2 (non-collinear, resp. non-concurrent);
- (H2) no two elements of $M(R)$ are at distance 2;
- (H3) $M(\Gamma_2(x)) = \Gamma_2(M(x))$ for every $x\in R$ (*$M$ is a local duality at $x$* when $M$ maps points to
  lines: it maps the points collinear with $x$ onto the lines concurrent with $M(x)$).

Then $t$ is repaired.

*Proof.* Write $j' = j+k$; "$\mathrm A$" and "$\mathrm B$" refer to $A(\tau_j), B(\tau_j)$ in level $j$ and to
$A(\tau_{j'}), B(\tau_{j'})$ in level $j'$. Elements of different types are at distance $\le 5$ in $I$. Take $(u,j)$ and
$(v,j')$.
1. $u\in \mathrm A$, $u\notin R$: $(u,j)\to(M(u),j')\leadsto(v,j')$: $\le 1+6$.
2. $u\in\mathrm B$, $v\in\mathrm A$: the $q+1\ge 2$ neighbours of $v$ are pairwise at distance 2, so by (H2) at most one
   is in $M(R)$; take $b\in\Gamma_1(v)\setminus M(R)$ and $a = M^{-1}(b)\notin R$:
   $(u,j)\leadsto(a,j)\to(b,j')\to(v,j')$: $\le 5+1+1$.
3. $u\in\mathrm B$, $v\in\mathrm B\setminus M(R)$: $(u,j)\leadsto(M^{-1}(v),j)\to(v,j')$: $\le 5+1$.
4. $u\in\mathrm B$, $v = M(x)$, $x\in R$: by (F3) there is $z\in\Gamma_2(x)$ with $d(z,u)\le 3$ ($x$ and $u$ have different
   types). By (H1) $z\notin R$; by (H3) $M(z)\in\Gamma_2(v)$: $(v,j')\leadsto(M(z),j')\to(z,j)\leadsto(u,j)$: $\le 2+1+3$.
5. $u = x\in R$, $v\in\mathrm A$: by (F3) there is $w\in\Gamma_2(M(x))$ with $d(w,v)\le 3$; by (H3) $w = M(z)$ with
   $z\in\Gamma_2(x)$, and $z\notin R$ by (H1): $(x,j)\leadsto(z,j)\to(w,j')\leadsto(v,j')$: $\le 2+1+3$.
6. $u = x\in R$, $v\in\mathrm B$: the same path, now with $d(w,v)\le 4$ by (F3) ($M(x)$ and $v$ have the same type):
   $\le 2+1+4$.

These cases cover all pairs ($u\in\mathrm A\setminus R$: 1; $u\in R$: 5, 6; $u\in\mathrm B$: 2, 3, 4). $\square$

Note that no hub is used: the earlier version of this theorem (research/d13D7/REPORT.md §2, with $R$ pairwise opposite)
routed case 6 through the hub of $x$; the route of case 6 above makes this unnecessary, which is what lets hubs take
their slots from different freed elements in different levels.

For a friendly transition with $M = \mathrm{id}$, (H3) holds at every element and (H2) is (H1), so Theorem B gives
Corollary 4.3.1 again; Theorem C is stronger there. Theorem B is needed for non-automorphic transitions. We now describe
its hypotheses for an $H\to H$ transition ($M: P\to L$); the $D\to D$ case is the same with $M^{-1}$.

For two points $x, y$ at distance 4 let $\mathrm{mid}(x,y)$ be the unique point collinear with both; for two lines at
distance 4 let $\mathrm{mid}(\ell,m)$ be the unique line concurrent with both.

**Proposition 5.1 (what (H1)–(H3) force).** Under (H1)–(H3), $M$ restricted to $R$ preserves distances, and
$M(\mathrm{mid}(x,y)) = \mathrm{mid}(M(x), M(y))$ for all $x, y\in R$ at distance 4.

*Proof.* Let $x\ne y\in R$; $d(x,y)\in\{4,6\}$ by (H1). If $d(x,y) = 4$, $m = \mathrm{mid}(x,y)\in\Gamma_2(x)\cap\Gamma_2(y)$,
so by (H3) $M(m)\in\Gamma_2(M(x))\cap\Gamma_2(M(y))$; hence $d(M(x),M(y))\le 4$, $=4$ by (H2), and $M(m)$ is the
mid-line. If $d(x,y) = 6$, $\Gamma_2(x)\cap\Gamma_2(y) = \emptyset$, so $\Gamma_2(M(x))\cap\Gamma_2(M(y)) = \emptyset$ by
(H3), and $d(M(x),M(y))\notin\{2,4\}$, i.e. $= 6$. $\square$

So $M(R)$ must *mirror* the distance-4 structure of $R$. The converse, in the form used for the records:

**Proposition 5.2 (mirrored sets).** Let $R$ be a non-collinear set of points, $R^*$ a non-concurrent set of lines and
$f: R\to R^*$ a bijection such that
- (M1) every point is collinear with at most two points of $R$, and every line is concurrent with at most two lines of
  $R^*$;
- (M2) for $x\ne y\in R$: $d(x,y) = 4$ if and only if $d(f(x),f(y)) = 4$.

Then there is a bijection $M: P\to L$ with $M\vert_R = f$ satisfying (H1)–(H3) for $R$. One such $M$ is: $M(x) = f(x)$
for $x\in R$; $M(\mathrm{mid}(x,y)) = \mathrm{mid}(f(x),f(y))$ for $x,y\in R$ at distance 4; for each $x\in R$, any
bijection from the remaining points of $\Gamma_2(x)$ onto the remaining lines of $\Gamma_2(f(x))$; any bijection on the rest.

*Proof.* Let $U = \bigcup_{x\in R}\Gamma_2(x)$ and $U^* = \bigcup_{x\in R}\Gamma_2(f(x))$. By (H1) for $R$ and $R^*$,
$R\cap U = \emptyset$ and $R^*\cap U^* = \emptyset$. A point of $U$ lies in $\Gamma_2(x)$ for one or two $x\in R$ (M1);
if two, $x$ and $y$ are at distance 4 (not collinear, and both collinear with it) and the point is $\mathrm{mid}(x,y)$.
So the points of $U$ in two sets $\Gamma_2(\cdot)$ correspond bijectively to the pairs $\{x,y\}\subseteq R$ at distance 4,
and likewise for $U^*$; by (M2) $\{x,y\}\mapsto\{f(x),f(y)\}$ is a bijection between these pairs. Hence the rule
$\mathrm{mid}(x,y)\mapsto\mathrm{mid}(f(x),f(y))$ is a bijection from the shared points of $U$ to the shared lines of
$U^*$, and it maps the shared points of $\Gamma_2(x)$ onto the shared lines of $\Gamma_2(f(x))$. The remaining
("private") points of $\Gamma_2(x)$ and private lines of $\Gamma_2(f(x))$ are then equally many (both $q(q+1)$ minus the
number of $y\in R$ at distance 4 from $x$), and private sets of different $x$ are disjoint. So the pieces define a
bijection $R\cup U\to R^*\cup U^*$ with $M(\Gamma_2(x)) = \Gamma_2(f(x))$ for every $x\in R$. As $\lvert P\setminus (R\cup U)\rvert
= \lvert L\setminus(R^*\cup U^*)\rvert$, it extends to a bijection $P\to L$. (H1), (H2) are the hypotheses on $R$ and
$R^*$. $\square$

**Corollary 5.3.**
(a) (Pairwise opposite sets; research/d13D7/REPORT.md.) If $R$ is a partial ovoid and $R^*$ a partial spread with
$\lvert R\rvert = \lvert R^*\rvert$, every bijection $f$ satisfies (M1), (M2) (there are no pairs at distance 4).
(b) (Mirrored sets; research/cell147/mirror/.) Let $R = R_0\cup X$ and $R^* = f(R_0)\cup\{L_x : x\in X\}$ with $R_0$, $X$
partial ovoids, $f(R_0)$ and $\{L_x\}$ partial spreads, $R$ non-collinear, $R^*$ non-concurrent. Then (M1) holds
automatically (three points of $R$ collinear with one point would be pairwise at distance 4, but two of them lie in $R_0$
or two in $X$, which are pairwise opposite), and (M2) says: for $r\in R_0$ and $x\in X$, $d(r,x) = 4$ if and only if
$d(f(r), L_x) = 4$.

In (b) the matching condition is a bipartite assignment problem: each $r\in R_0$ has a "type", the set of $x\in X$ at
distance 4 from it, and must be sent to a spread line of the same type with respect to the lines $L_x$. The record sets
were found by annealing over $X$, $L_x$ and $f$ (research/cell147/mirror/mirror_sa*.py), and every one was re-checked by
the builder (non-collinearity, non-concurrency, and (H3) at every $x\in R$, directly).

---

## 6. Typed level layouts and slot counts

By Theorem 3.4 the order is $(2r+1)\cdot 2N + K_{\mathcal A} + K_{\mathcal B}$ with
$K_{\mathcal B}\le\min_j\alpha_j$ and $K_{\mathcal A}\le\min_j\beta_j$, where $\alpha_j$ ($\beta_j$) counts the freed
elements of the transitions leaving (entering) level $j$. Which transitions are friendly depends on the types.

**All levels of type $H$, one bijection $\sigma$, one freed set $R$ on every transition** (the three-level records
(7,7), (9,7), (10,7), (13,7) with $\sigma$ a local duality on $R$, and (11,7), (12,7) with $\sigma$ a duality). Every
level has
$\alpha_j = \beta_j = r\lvert R\rvert$, so $K_{\mathcal A} = K_{\mathcal B} = r\lvert R\rvert$ and
$$\lvert X_R^+\rvert = (2r+1)\cdot 2N + 2r\lvert R\rvert .$$
Hubs: for $r = 1$ the $\mathcal B$-hub $h_x$ of $x\in R$ is joined to $(x,0),(x,1),(x,2)$ and the $\mathcal A$-hub $g_x$
to $(\sigma(x),0),(\sigma(x),1),(\sigma(x),2)$, plus $q-1$ hub-graph edges each.

**Types $HDHDH$ ($r = 2$).** Transitions $j\to j+1$ and $j\to j+2$. Friendly: $0\to1$, $2\to3$, $4\to1$ ($H\to D$,
points freed) and $1\to2$, $3\to4$, $3\to0$ ($D\to H$, lines freed). Not friendly: $0\to2$, $2\to4$, $4\to0$ ($H\to H$)
and $1\to3$ ($D\to D$). With $F_t$ the freed sets:

| level | type | free $\mathcal A$-slots $\alpha_j$ | free $\mathcal B$-slots $\beta_j$ |
|---|---|---|---|
| 0 | H | $F_{0\to1} + R_{0\to2}$ | $R_{4\to0} + F_{3\to0}$ |
| 1 | D | $F_{1\to2} + R_{1\to3}$ | $F_{0\to1} + F_{4\to1}$ |
| 2 | H | $F_{2\to3} + R_{2\to4}$ | $F_{1\to2} + R_{0\to2}$ |
| 3 | D | $F_{3\to4} + F_{3\to0}$ | $F_{2\to3} + R_{1\to3}$ |
| 4 | H | $R_{4\to0} + F_{4\to1}$ | $F_{3\to4} + R_{2\to4}$ |

(sizes of the sets). With all point sets of size $f_P$, all line sets of size $f_L$, and $m$ elements freed on each
non-friendly transition: $K_{\mathcal B}\le\min(f_P+m,\ f_L+m,\ 2f_L)$ and
$K_{\mathcal A}\le\min(f_L+m,\ 2f_P,\ f_P+m)$. Five levels and two matchings form the regular tournament on 5 vertices;
a 3+2 split of the types cuts 6 of the 10 arcs, the maximum, and gives every level one friendly outgoing and one friendly
incoming transition at least. (With three levels, some level always has no friendly outgoing transition, so typing
does not help for $r = 1$.)

**Seven levels ($r = 3$).** The (15,7) graph uses types $HHDHDHD$: 12 of the 21 transitions are friendly and every level
has at least one friendly transition in each direction (research/d15D7b/README.md).

---

## 7. Hub graphs

Condition (HG) of Theorem 3.4 asks for a bipartite graph $Y$ on $K_{\mathcal B} + K_{\mathcal A}$ hubs with maximum
degree $\le q - r$ in which same-colour hubs are within distance 6 (possibly helped by paths through the levels). This
is a purely combinatorial side condition. Write $\mathrm{HG}(K_1,K_2;d)$ for a bipartite graph with colour classes of
sizes $K_1, K_2$, maximum degree $\le d$, and all same-colour distances $\le 6$.

**Lemma 7.1 (plane with pendant trees).** Let $s$ be a prime power and $t, u\ge 0$ integers with $s+1+t\le d$ and
$u+1\le d$. Then $\mathrm{HG}(K,K;d)$ exists for every $K$ with $s^2+s+1\le K\le (s^2+s+1)(1+t+tu)$.

*Proof.* Start from the incidence graph of $\mathrm{PG}(2,s)$ (the *core*: diameter 3, same-colour distance 2). Attach
to some core vertices up to $t$ pendant vertices each ("depth 1", of the opposite colour), and to some depth-1 vertices
up to $u$ pendant vertices each ("depth 2", of the colour of the core vertex). Degrees are at most $s+1+t$, $u+1$ and
$1$. For two vertices $x, y$ of the same colour with core ancestors $c(x), c(y)$,
$d(x,y)\le \mathrm{depth}(x)+d(c(x),c(y))+\mathrm{depth}(y)$. The core ancestors have the same colour when the depths
have the same parity (core distance $\le 2$) and different colours otherwise (core distance $\le 3$); the possible totals
are $0+2+0$, $0+3+1$, $0+2+2$, $1+2+1$, $1+3+2$, $2+2+2$, all $\le 6$. To get $K$ vertices of each colour, give $c$ depth-1
children to the points and $c$ to the lines, and $g$ depth-2 children below each of these two families, with
$c = \lceil (K-s^2-s-1)/(1+u)\rceil\le (s^2+s+1)t$ and $g = K-s^2-s-1-c\le uc$. $\square$

Taking $t = d-s-1$ and $u = d-1$, Lemma 7.1 gives hub graphs with up to
$\kappa(d) := \max_s (s^2+s+1)(1+(d-s-1)d)\approx \tfrac{4}{27}d^4$ vertices per colour ($s$ over prime powers
$\le d-1$; $\kappa(4) = 35$, $\kappa(8) = 527$, $\kappa(9) = 868$, $\kappa(10) = 1{,}271$, $\kappa(11) = 1{,}938$). For
$d\ge 3$ the intervals for $s = 2$ and for the optimal $s$ overlap, so $\mathrm{HG}(K,K;d)$ exists for every
$7\le K\le\kappa(d)$. This is enough for the general statements of Section 9 but far below what the records need. The
record hub graphs were found by computer and checked:

| cell | hubs per colour | hub degree | hub graph | (HG) checked by |
|-----------|----------|------|----------------------------------------|------------------------------|
| (7,7), (9,7), (10,7), (13,7) | 81, 295, 229, 768 | $q-1$ | random $(q-1)$-regular, retried until same-colour distances $\le 6$ in $Y$ | research/d13D7/multi.c (BFS in $Y$), then the full all-pairs check |
| (11,7) | 7,300 | 8 | Haar graph of $\mathbb Z_{73}\rtimes\mathbb Z_{100}$, diameter 7 | build_haar2.py, then full check |
| (12,7) | 14,600 | 7 | Haar graph of $(\mathbb Z_{73}\rtimes\mathbb Z_8)\times\mathbb Z_5^2$, with paths through the levels ("cluster-assisted", research/squads/cells/d12D7.md §2) | full check |
| (14,7) | 9,014 | 9 | 9 random perfect matchings | BFS in $Y$, then full check |
| (15,7) | 10,826 / 10,481 | $\le 8$ | random, repaired by 2-switches; paths through the levels allowed | BFS from all hubs, then full check |
| (16,7) | 14,884 | $\le 11$ | voltage graph over $\mathbb Z_{61}$ | hubcheck.c, then full check (with automorphism) |

---

## 8. The record graphs as corollaries

In each case below the graph is $X_R^+$ of Definition 3.1, every transition is repaired by Theorem B or C, and (HG) holds,
so Theorem 3.4 gives the bound. "Computer" marks the parts that are found by search and checked by computer rather than
proved in general: the specific sets, the bijection $f$, and the hub graph. The theorems themselves are proved for all
$q$.

**Corollary 8.1 (three levels, one local duality: (7,7), (9,7), (10,7), (13,7)).** Let $r = 1$, all types $H$,
$M_t = \sigma$ for all three transitions and $R_t = R$ for all three, with $(R,\sigma)$ as in Proposition 5.2 /
Corollary 5.3(b). If $\mathrm{HG}(\lvert R\rvert,\lvert R\rvert; q-1)$ exists, then
$$n_b(q+2,\,7)\ \ge\ 6N(q) + 2\lvert R\rvert .$$
Records: $q = 5$: $\lvert R\rvert = 81$ ($R_0$ = 72 pairwise opposite points, 9 extra points, spread lines of
$q^3+1 = 126$ available), $n = 23{,}598$; $q = 7$: $288 + 7$, $n = 118{,}238$; $q = 8$: $217 + 12$, $n = 225{,}152$;
$q = 11$: $756 + 12$, $n = 1{,}064{,}472$. Computer: $R_0$ (for $q = 7, 11$ an orbit of the Weyl group $W(E_7)$ acting on $Q(6,q)$ through the $E_7$ root
lattice mod $q$, research/cell147/ovoid/ and octo/ on the cell-14-7 branch; being pairwise non-orthogonal in $Q(6,q)$ it is
a partial ovoid of $H(q)$ by (F4); for $q = 5, 8$ from research/d13D7/q57, q8), the extra points $X$, the lines $L_x$,
the bijection $f$ onto Hermitian spread lines, the hub graph.

**Corollary 8.2 (duality, $q = 3^h$: (11,7), (12,7)).** Let $q = 3^h$, $\varphi$ a duality, all types $H$, $M_t = \varphi\vert_P$
for every transition, and $R_t = F$ for every transition, $F$ the point set of a spread (e.g. the Hermitian spread),
$\lvert F\rvert = (q+1)(q^3+1)$. By Theorem C every transition is repaired. Every level has $r\lvert F\rvert$ free slots of
each colour. If $\mathrm{HG}(K,K;q-r)$ exists, $K\le r(q+1)(q^3+1)$, then
$$n_b(q+1+r,\,7)\ \ge\ (2r+1)\cdot 2N(q) + 2K .$$
Records ($q = 9$, $\lvert F\rvert = 7{,}300$): $r = 1$, $K = 7{,}300$: $n = 413{,}180$; $r = 2$, $K = 14{,}600$:
$n = 693{,}500$. By Proposition 1.4 this is the largest freed set that Theorem C allows, so $K = r(q+1)(q^3+1)$ is the cap
of this construction. Computer: the duality $\varphi$ of $H(9)$ (explicit, verified), the hub graphs. Proved: the freed set
and its size, for every $q = 3^h$.

**Corollary 8.3 (typed levels: (14,7), (15,7), (16,7)).** Let the types be $HDHDH$ ($r = 2$) or $HHDHDHD$ ($r = 3$), let
every friendly transition carry $M_t = \mathrm{id}$ and a segment set (points) or dual segment set (lines) $F_t$, and let
the non-friendly transitions carry $M_t = \sigma$ ($H\to H$) or $\sigma^{-1}$ ($D\to D$) with freed sets $R$
(resp. $\sigma(R)$) satisfying Theorem B. If $\mathrm{HG}(K_{\mathcal B},K_{\mathcal A};q-r)$ exists with
$K_{\mathcal B}\le\min\alpha_j$, $K_{\mathcal A}\le\min\beta_j$ (Section 6), then
$$n_b(q+1+r,\,7)\ \ge\ (2r+1)\cdot 2N(q) + K_{\mathcal A} + K_{\mathcal B}.$$
Records:
- (14,7), $q = 11$, $HDHDH$: all friendly point sets equal one non-collinear set of 8,645 points, all friendly line sets
  one non-concurrent set of 8,246 lines (both unions of orbits of an order-133 collineation), and the 768-point mirrored
  set of Corollary 8.1 on the four non-friendly transitions. $\alpha = (9413, 9014, 9413, 16492, 9413)$,
  $\beta = (9014, 17290, 9014, 9413, 9014)$, $K_{\mathcal A} = K_{\mathcal B} = 9{,}014$: $n = 1{,}789{,}588$.
- (15,7), $q = 11$, $HHDHDHD$: twelve friendly sets with 5,674–9,303 elements each; in the four bottleneck sets some
  elements have one partner (5,577 pairs in all), so these are segment sets but not non-collinear; the 768-point
  mirrored set on the nine non-friendly transitions. $K_{\mathcal B} = 10{,}826$, $K_{\mathcal A} = 10{,}481$:
  $n = 2{,}501{,}491$. (The graph also satisfies the lab's unnecessary hub condition (R2).)
- (16,7), $q = 13$, $HDHDH$: a non-collinear set of 14,762 points and a non-concurrent set of 14,823 lines (unions of
  orbits of an order-61 element of $SL(3,13)$), and on the four non-friendly transitions a pairwise opposite set of 122
  points (resp. lines) with $\sigma$ as in Corollary 5.3(a). $K_{\mathcal A} = K_{\mathcal B} = 14{,}762 + 122 = 14{,}884$:
  $n = 4{,}052{,}108$.

Computer: all these sets, $\sigma$, and the hub graphs.

---

## 9. What is proved for every $q$

Theorems A, B, C and 3.4 hold for every prime power $q$ (the proofs only use (F1)–(F3), and at least two points on a
line and two lines on a point). What is not known in general is how large the sets can be made and whether large hub
graphs exist; Lemma 1.2 and Lemma 7.1 give explicit choices. With $\kappa(d)$ as in Section 7:

**Corollary 9.1 (every $q\ge 4$, three levels).** With $R$ the $q^2+1$ points of an elliptic quadric $Q^-(3,q)$ section
(Lemma 1.2(a)) and $R^*$ any $q^2+1$ lines of the Hermitian spread (Corollary 5.3(a)):
$$n_b(q+2,\,7)\ \ge\ 6N(q) + 2\min\bigl(q^2+1,\ \kappa(q-1)\bigr),$$
which is $6N(q)+2(q^2+1)$ for every $q\ge 5$.

**Corollary 9.2 ($q = 3^h$).** For every $r$ with $1\le r\le q-3$ (Corollary 8.2 with Lemma 7.1):
$n_b(q+1+r,\,7)\ \ge\ (2r+1)\cdot 2N(q) + 2\min\bigl(r(q+1)(q^3+1),\ \kappa(q-r)\bigr)$.

**Corollary 9.3 (every $q\ge 5$, typed levels $HDHDH$).** Friendly point sets: the point set of the Hermitian spread
($(q+1)(q^3+1)$ points); friendly line sets: the lines through the points of an elliptic quadric section
($(q+1)(q^2+1)$ lines, a dual segment set); non-friendly: $m = q^2+1$ as in Corollary 9.1. By the table of Section 6 the smallest slot counts are
$\min_j\alpha_j = \min_j\beta_j = (q+1)(q^2+1) + q^2+1 = (q+2)(q^2+1)$, so
$$n_b(q+3,\,7)\ \ge\ 10N(q) + 2\min\bigl((q+2)(q^2+1),\ \kappa(q-2)\bigr).$$

The record values exceed these because the sets found by computer are of order $q^4$ (non-collinear sets of 8,645 and
14,762 points at $q = 11, 13$, against $q^4 = 14{,}641$, $28{,}561$) and the hub graphs found by computer are much larger
than $\kappa$. For $q = 3^h$ the sets are already optimal for Theorem C (Proposition 1.4) and only the hub graphs are
found by computer.

**Remark 9.4 (consequences of Theorem C not yet built).** Theorem C allows friendly sets that are much larger than the
non-collinear and non-concurrent sets used in the (14,7)–(16,7) records: up to $(q+1)(q^3+1)$ (Proposition 1.4), e.g.
the 15,984 points of the Hermitian spread of $H(11)$ against 8,645, and the $12\cdot 756 = 9{,}072$ lines through the
756-point partial ovoid of $H(11)$ against 8,246 (non-concurrent). In the $HDHDH$ layout with these sets and the 768
mirrored elements the slot counts of Section 6 give $K_{\mathcal A} = K_{\mathcal B} = 9{,}072+768 = 9{,}840$, i.e.
$n = 1{,}771{,}560 + 19{,}680 = 1{,}791{,}240$ at (14,7), provided a hub graph with 9,840 hubs per colour and degree 9
exists. We have not built or checked these graphs; they are left to the lab's search sessions.

---

## 10. Computer checks

### 10.1 Small-$q$ tests of every theorem

Two independent sets of programs (details, commands and logs in the two README files):
- research/theorems/d7hex_tests/: builds $H(q)$ from scratch from the coordinates of Section 1.1 ($q = 2,3,4,5$), builds
  each graph from Definitions 2.1 and 3.1 (asserting that every matching is a bijection), and checks it with
  research/lifts/coordinator_check/apsp_mt.c (breadth-first search from every vertex; "VALID" = bipartite, maximum degree
  $\le\Delta$, diameter $\le 7$);
- research/theorems/d7hex_lemma41/: uses the lab's generator research/d10D7/hexgen2.c and duality finder
  research/d10D7/dual/dualfind.c; checks Lemma 4.1 directly on all ordered pairs $(u,v)$, and the duality construction.

| statement | what was built | $q$ | result |
|--------------|----------------------------------------------------|------|------------------------------|
| §1.1 coordinates, (F1), (F4), Lemma 1.2(b) | $H(q)$ from Tits' equations; counts, diameter 6, girth 12 (distance profile), (F4) on all pairs ($q\le 4$) or a sample ($q = 5$); Hermitian spread in $x_0 = c x_4 + e x_3$ | 2, 3, 4, 5 | all hold; spreads of 28, 65, 126 pairwise opposite lines |
| Theorem A | plain level covers with random bijections, types $HHH$, $HDH$, $HHHHH$, $HDHDH$ (and $HHDHHDD$, $HHHHHHH$ for $q = 3, 4$) | 3, 4, 5 | all VALID, $(q+1+r)$-regular |
| Lemma 4.1 | all ordered pairs, for spread-point sets, three random maximal segment sets, a random maximal (R1) set; points and lines | 3, 4, 5 | 0 failures; each set plus one turning point: 36–320 failing pairs |
| Theorem C (friendly) | two levels $H\to D$, $D\to H$ and five levels $HDHDH$, main graph without hubs, with: all points of the Hermitian spread (112, 325, 756 $=(q+1)(q^3+1)$), random maximal segment sets, (R1) sets with no hub condition, pencils of a partial ovoid, dual segment sets; 3 seeds | 3, 4, 5 | 108 of 108 VALID; set plus one turning point: 72–1,800 ordered pairs at distance $>7$ (apsp_mt: diameter 8, INVALID) |
| Theorem C (duality), Cor. 8.2 | all levels $H$, every transition matched by a polarity $\varphi$ of $H(3)$, the 112 spread points freed on every transition, $r = 1, 2$ | 3 | VALID ($n = 2{,}184$ and $3{,}640$); one more point freed: diameter 8 |
| Theorem B, Prop. 5.2, Cor. 5.3 | $M$ built exactly as in Proposition 5.2, (H1)–(H3) re-checked on it; $R$ pairwise opposite (an ovoid of 28 points at $q = 3$; 23; 33) and mirrored $R$ with pairs at distance 4 (17 points/19 pairs; 26/21; 38/28); types $HHH$ (same $M$, $R$ on all transitions) and $HDHDH$ ($M$ on $H\to H$, $M^{-1}$ on $D\to D$) | 3, 4, 5 | all VALID; breaking (H3) at one point: 50, 76, 126 ordered pairs at distance $>7$ |
| Theorem 3.4 (hubs) | full graphs with hubs on random free slots and a random hub graph of degree $\le q-r$: $HHH$, $HDH$ ($K$ = slot minimum, 28 and 35), $HDHDH$ ($K$ = 48 and 61, below the slot minimum because the hub degree $q-2$ is small) | 4, 5 | all VALID ($n$ = 8,246, 8,246, 13,746; 23,506, 23,506, 39,182) |

Every positive test passed and every negative control failed. Small $q$ cannot test the hub graphs at the record sizes
(at $q\le 5$ the hub degree $q-r$ is 1 to 4); for those see Section 10.2.

### 10.2 The record graphs

Each record graph was rebuilt by the lab's coordinator (on a separate machine) from its solution file with the session's
builder, which also re-checks the hypotheses ((H1)–(H3) at every freed element, non-collinearity or the partner condition
of the friendly sets, degrees, the hub graph). The edge list was then checked by
research/lifts/coordinator_check/apsp_mt.c: simple graph, maximum degree $\le\Delta$, bipartite, connected, and a
bit-parallel breadth-first search from **every** vertex, no symmetry assumed. All nine runs are in
research/coordinator_check/check_2026-10-25.txt:

| cell | $n$ | apsp_mt output (all sources) |
|----------|------------:|----------------------------------------|
| (7,7) | 23,598 | RESULT VALID d=7 D=7 n=23598 |
| (9,7) | 118,238 | RESULT VALID d=9 D=7 n=118238 |
| (10,7) | 225,152 | RESULT VALID d=10 D=7 n=225152 |
| (11,7) | 413,180 | RESULT VALID d=11 D=7 n=413180 |
| (12,7) | 693,500 | RESULT VALID d=12 D=7 n=693500 |
| (13,7) | 1,064,472 | RESULT VALID d=13 D=7 n=1064472 |
| (14,7) | 1,789,588 | RESULT VALID d=14 D=7 n=1789588 |
| (15,7) | 2,501,491 | RESULT VALID d=15 D=7 n=2501491 |
| (16,7) | 4,052,108 | RESULT VALID d=16 D=7 n=4052108 |

(The finders' own checks were partly reduced by symmetry, e.g. an order-61 automorphism for (16,7); the coordinator's
runs above assume none.)

---

## 11. Prior art, and what is new

*Classical.* Generalized hexagons and their incidence graphs (Tits 1959); the split Cayley hexagon in $Q(6,q)$, its
dualities for $q = 3^h$, and the Hermitian spread (Tits; Thas 1980; Van Maldeghem's book [VM98]). Building large
bipartite graphs of given degree and diameter from several copies of the incidence graph of a generalized polygon joined by
matchings ("duplication", levels) goes back to Delorme [De85a, De85b] (with Farhi [DF84] for duplication in general);
several of the old D = 4 and D = 6 values of the 2013 table come from these constructions. The D = 7 values with
$\Delta\ge 9$, and (7,7), have exactly the form $(2r+1)\cdot 2N(q)$ of Theorem A. We have not checked which reference
the table cites for each D = 7 cell, and we do not claim Theorem A as new: it is the routine argument for such covers.

*New here (as far as we know).* Deleting matching edges at freed elements and reattaching the freed slots to hub vertices
(Definition 3.1, Theorem 3.4); the repair theorems B and C; the use of dual levels ("typed levels") to make transitions
automorphic; segment sets and Proposition 1.4; mirrored sets (Propositions 5.1, 5.2); and the nine values in Section 0.

## References

- [BGS06] S. Ball, P. Govaerts, L. Storme, On ovoids of parabolic quadrics, Des. Codes Cryptogr. 38 (2006) 131–145.
- [DF84] C. Delorme, G. Farhi, Large graphs with given degree and diameter, Part I, IEEE Trans. Computers C-33 (1984)
  857–860.
- [De85a] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302.
- [De85b] C. Delorme, Large bipartite graphs with given degree and diameter, J. Graph Theory 9 (1985) 325–334.
- [MS13] M. Miller, J. Širáň, Moore graphs and beyond: a survey of the degree/diameter problem, Electron. J. Combin.,
  Dynamic Survey DS14 (2nd ed., 2013).
- [Th80] J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A 29 (1980) 87–93.
- [Th81] J. A. Thas, Ovoids and spreads of finite classical polar spaces, Geom. Dedicata 10 (1981) 135–143.
- [Ti59] J. Tits, Sur la trialité et certains groupes qui s'en déduisent, Publ. Math. IHÉS 2 (1959) 13–60.
- [VM98] H. Van Maldeghem, Generalized Polygons, Birkhäuser, 1998.
