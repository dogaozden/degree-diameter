---
title: "Ball lifts of the split Cayley hexagon: bipartite graphs of diameter 9, 10 and 11"
author: "Degree–diameter lab (Claude Code sessions coordinated by Doğa Özden)"
date: "Draft, 28 October 2026"
---

Draft of 28 October 2026 (job thm-polygon-levels; branch `claude/haiku-squads-diameter-7-hr64vz` of
github.com/dogaozden/degree-diameter). Written in the style of the lab's diameter-7 note
(research/theorems/D7_HEXAGON.md on branch `claude/d7-hexagon-theorems-4w1prt`, "the D7 note"), whose coordinates and
notation are used. Every claim is labelled **Theorem** (proved here, by hand), **Computer-checked** (a statement about
specific finite objects, with the check named) or **Heuristic** (an argument with a gap that is named).

RESULTS_PLACEHOLDER

# 1. Notation

Throughout, $q$ is a prime power and $H = H(q)$ is the split Cayley hexagon in the coordinates of the D7 note, §1.1:
$V = \mathbb F_q^7$ with coordinates $(X_0,\dots,X_6)$, the parabolic quadric
$$Q(X) = X_0X_4 + X_1X_5 + X_2X_6 - X_3^2,$$
with polar form $b(X,Y) = Q(X+Y)-Q(X)-Q(Y)$. The points of $H$ are the $N$ points of $Q(6,q)$,
$$N = N(q) = \frac{q^6-1}{q-1} = (q+1)(q^4+q^2+1) = (q^3+1)(q^2+q+1),$$
the lines are the $N$ lines of $Q(6,q)$ whose Grassmann coordinates satisfy Tits' equations
$p_{12}=p_{34}$, $p_{54}=p_{32}$, $p_{20}=p_{35}$, $p_{65}=p_{30}$, $p_{01}=p_{36}$, $p_{46}=p_{31}$, and incidence is
containment. $P$ and $L$ denote the point and line sets.

$I = I(q)$ is the incidence graph of $H$ (vertex set $P\cup L$, $2N$ vertices, $(q+1)$-regular, bipartite), $d$ its
distance. $H$ is a generalized hexagon of order $(q,q)$, so (D7 note §1.2):

* (F1) $I$ has diameter 6 and girth 12; point–line distances are $1,3,5$ and same-type distances $0,2,4,6$.
* (F2) if $d(x,y)\le 5$ there is a unique shortest path from $x$ to $y$.

For a point $x$, the lines of $H$ through $x$ are the $q+1$ lines through $x$ of a totally singular plane $\pi_x$
of $Q(6,q)$, and the points at distance $\le 2$ from $x$ in $I$ are exactly the $q^2+q+1$ points of $\pi_x$
(each line through $x$ contributes its $q$ further points).

**Balls.** For an element $x$ and an even $\rho\ge 0$, $B_\rho(x)$ is the set of elements **of the same type** as $x$
at distance $\le\rho$ from $x$. So $B_0(x)=\{x\}$; $B_2(p)=\pi_p$ for a point $p$; $B_2(l)$ is $l$ together with the
$q(q+1)$ lines meeting $l$; and $|B_2(x)| = q^2+q+1$ for every $x$. A set $A$ of elements of one type is
**$\rho$-dominating** if it meets $B_\rho(x)$ for every element $x$ of that type.

**Ovoids and spreads.** An ovoid of $H$ is a set of $q^3+1$ pairwise opposite points (distance 6); a spread is a set of
$q^3+1$ pairwise opposite lines. Every element is at distance $\le 2$ from exactly one element of an ovoid (resp. spread)
of its type: two elements of an ovoid cannot share a 2-ball (they would be at distance $\le 4$), and
$(q^3+1)(q^2+q+1) = N$. Spreads exist for every $q$ (the Hermitian spread: the lines of $H$ contained in a hyperplane
section $Q^-(5,q)$); ovoids exist when $q$ is a power of 3 (then $H\cong H^D$ and a duality maps a spread to an ovoid); see §9 for
non-existence results.

# 2. The ball lift

The construction works for any bipartite graph in place of $I$; the hexagon enters only through the numbers in
Corollaries 3.1, 4.2 and 5.1. Fix:

* a connected bipartite graph $I$ with colour classes $P$ ("points") and $L$ ("lines"), $|P| = |L| = N$, in which every
  point–line distance is at most an odd number $c$;
* an even $\rho\ge 0$ and integers $k, r\ge 1$;
* partitions $P = A_0\cup\dots\cup A_{k-1}$ and $L = B_0\cup\dots\cup B_{k-1}$ with $|A_i| = |B_i|$, such that every
  $A_i$ is $\rho$-dominating (meets $B_\rho(p)$ for every point $p$) and every $B_i$ is $\rho$-dominating (meets
  $B_\rho(l)$ for every line $l$);
* bijections $\sigma_1,\dots,\sigma_r : P\to L$ with $\sigma_t(A_i) = B_i$ for all $t, i$.

Put $m = 2rk+1$ and, for $z\in A_i$ and $1\le t\le r$, $\;e_t(z) = (t-1)k + i + 1\in\{1,\dots,rk\}$.

**Definition 2.1 (the ball lift $\Lambda = \Lambda(I;A,B,\sigma;r)$).** The vertex set is $(P\cup L)\times\mathbb Z_m$.
The neighbours of a point vertex $(z,g)$, $z\in A_i$, are
$$(l,g)\ \ (l\ni z), \qquad (\sigma_t(z),\, g + (t-1)k + i + 1)\ \ (1\le t\le r);$$
the neighbours of a line vertex $(l,g)$, $l\in B_i$, are
$$(p,g)\ \ (p\in l),\qquad (\sigma_t^{-1}(l),\, g - (t-1)k - i - 1)\ \ (1\le t\le r)$$
(note $\sigma_t^{-1}(l)\in A_i$, so the two lists describe the same edges). In words: $m$ copies ("layers") of $I$,
and $r$ perfect matchings between points and lines, the edge at $z$ of the $t$-th matching climbing $e_t(z)$ layers.

**Lemma 2.2 (Theorem).** Let $\Gamma$ be a connected bipartite graph with at least one edge.
(a) If any two vertices of the same colour are at distance $\le 2s$, then $\operatorname{diam}\Gamma\le 2s+1$.
(b) If any two vertices of different colours are at distance $\le 2s-1$, then $\operatorname{diam}\Gamma\le 2s$.

*Proof.* (a) Let $u, v$ have different colours and let $v'$ be a neighbour of $v$ (it exists: $\Gamma$ is connected
with an edge). $v'$ has the colour of $u$, so $d(u,v)\le d(u,v')+1\le 2s+1$. (b) The same with $u, v$ of the same
colour. $\square$

**Theorem 2.3.** $\Lambda$ is a simple bipartite graph on $2Nm$ vertices in which every vertex has degree
$\deg_I(x) + r$, and
$$\operatorname{diam}\Lambda\ \le\ \rho + c + 2 .$$

*Proof.* *Simple and bipartite.* Every edge joins $P\times\mathbb Z_m$ to $L\times\mathbb Z_m$. An edge of $I$ keeps the
layer; the $t$-th matching edge at $(z,g)$ changes it by $e_t(z)\in[(t-1)k+1,\,tk]$, which is never $0$ modulo
$m = 2rk+1$, and differs for different $t$. So no edge is repeated, and each vertex has $\deg_I(x)$ edges inside
its layer and $r$ matching edges.

*Translations.* $\tau_h:(x,g)\mapsto(x,g+h)$ is an automorphism, so it suffices to bound distances from vertices in
layer 0. Write $F = \{1,\dots,rk\}$; then $\mathbb Z_m = \{0\}\cup F\cup(-F)$, a disjoint union, and every $h\in F$
is $(t-1)k+i+1$ for exactly one pair $(t,i)$.

*Two points.* Let $p, p'\in P$ and $h\in\mathbb Z_m$; we show $d((p,0),(p',h))\le\rho+c+1$.

* $h = 0$: inside layer 0, $d_I(p,p')\le c+1$ (go from $p$ to a line through $p'$, then to $p'$).
* $h = (t-1)k+i+1\in F$: choose $z\in A_i\cap B_\rho(p)$. The walk
  $(p,0)\leadsto(z,0)\to(\sigma_t(z),h)\leadsto(p',h)$ has length $\le\rho + 1 + c$ (the middle edge is the $t$-th
  matching edge at $z$, which climbs $e_t(z) = h$ layers; the last segment is a point–line path of $I$ inside layer
  $h$).
* $h = -((t-1)k+i+1)\in -F$: choose $z\in A_i\cap B_\rho(p')$. The walk
  $(p,0)\leadsto(\sigma_t(z),0)\to(z,h)\leadsto(p',h)$ has length $\le c+1+\rho$.

*Two lines.* Let $l, l'\in L$.

* $h = 0$: $\le c+1$ inside layer 0.
* $h = -((t-1)k+i+1)$: choose $w\in B_i\cap B_\rho(l)$; then $\sigma_t^{-1}(w)\in A_i$ and the walk
  $(l,0)\leadsto(w,0)\to(\sigma_t^{-1}(w),h)\leadsto(l',h)$ has length $\le\rho+1+c$.
* $h = (t-1)k+i+1$: choose $w\in B_i\cap B_\rho(l')$; the walk
  $(l,0)\leadsto(\sigma_t^{-1}(w),0)\to(w,h)\leadsto(l',h)$ has length $\le c+1+\rho$.

So any two vertices of the same colour are within $\rho+c+1$ (an even number). In particular $\Lambda$ is connected
(every vertex has a neighbour), and Lemma 2.2(a) gives $\operatorname{diam}\Lambda\le\rho+c+2$. $\square$

**Remark 2.4 (the classical case).** $\rho = 0$, $k = 1$, $A_0 = P$, $B_0 = L$: the hypotheses hold trivially
($B_0(x) = \{x\}$) and $\Lambda$ is the level graph with $2r+1$ layers and arbitrary matchings, of diameter $\le c+2$.
For $H(q)$ ($c = 5$) this is Theorem A of the D7 note (the 2013 table's diameter-7 values $(2r+1)\cdot 2N(q)$); for a
generalized quadrangle ($c=3$) it is the diameter-5 polygon cover. The point of Theorem 2.3 is that a jump may start
anywhere in a ball of radius $\rho$, so $\rho$ more steps of diameter buy a factor $\approx|B_\rho|$ in the number of
layers instead of a factor $\approx r$.

**Remark 2.5 (relaxed data).** The partitions can be replaced by pairwise disjoint $\rho$-dominating families
$D_0,\dots,D_{k-1}\subseteq P$ and $E_0,\dots,E_{k-1}\subseteq L$ with
$\sum_i\max(|D_i|,|E_i|)\le N$: enlarge the smaller of $D_i, E_i$ by unused elements until $|D_i| = |E_i|$, then
distribute the rest evenly (enlarging a dominating set keeps it dominating). This is the balance condition checked by
the scorer `research/theorems/polylev/domcheck.py`.

**Remark 2.6 (dualities).** If $\varphi$ is a duality of $H$ (an incidence-preserving bijection $P\cup L\to L\cup P$
exchanging the types), then $\varphi$ maps $B_\rho(p)$ onto $B_\rho(\varphi(p))$, so $\varphi(A_i)$ is a
$\rho$-dominating set of lines with $|\varphi(A_i)| = |A_i|$. Hence when $q$ is a power of 3, a point partition alone
suffices: take $B_i = \varphi(A_i)$ and $\sigma_t = \varphi|_P$ (or any bijection with $\sigma_t(A_i) = B_i$).

# 3. Diameter 9 from $H(q)$

**Corollary 3.1 (Theorem).** Let $A_0,\dots,A_{k-1}$ be a partition of the points of $H(q)$ in which every $A_i$ meets
every plane $\pi_p$ ($p\in P$), and $B_0,\dots,B_{k-1}$ a partition of the lines in which every $B_i$ contains, for
every line $l$, the line $l$ or a line meeting $l$; suppose $|A_i| = |B_i|$. Then for every $r\ge 1$ there is a
bipartite $(q+1+r)$-regular graph of diameter at most 9 with
$$2N(q)\,(2rk+1)\ \text{ vertices.}$$
The graph is $\Lambda$ of Definition 2.1 with $I = I(q)$ (so $c = 5$), $\rho = 2$ and any bijections $\sigma_t$ with
$\sigma_t(A_i) = B_i$; Theorem 2.3 gives the diameter. Explicitly, the neighbours of $(z,g)$, $z\in A_i$, are the $q+1$
vertices $(l,g)$ with $l\ni z$ and the $r$ vertices $(\sigma_t(z), g+(t-1)k+i+1)$; the neighbours of $(l,g)$,
$l\in B_i$, are the $q+1$ vertices $(p,g)$ with $p\in l$ and the $r$ vertices $(\sigma_t^{-1}(l), g-(t-1)k-i-1)$.

**Proposition 3.2 (Theorem).** In Corollary 3.1, $k\le q^2+q+1$, with equality if and only if every $A_i$ is an ovoid
and every $B_i$ is a spread. Hence $k = q^2+q+1$ needs $H(q)$ to have ovoids (they exist when $q$ is a power of 3; $H(2)$ has none, Computer-checked 3.3; see §9 for what is known in general).

*Proof.* A point $z$ lies in $\pi_p$ exactly for the $q^2+q+1$ points $p\in\pi_z$. Since $A_i$ meets all $N$ planes,
$|A_i|(q^2+q+1)\ge N$, i.e. $|A_i|\ge q^3+1$, and $\sum_i|A_i| = N$ gives $k\le q^2+q+1$. Equality forces
$|A_i| = q^3+1$ and every plane to meet $A_i$ exactly once; then two points of $A_i$ are never collinear (both would lie
in $\pi_z$ for one of them) and never at distance 4 (both would lie in $\pi_y$ for the middle point $y$ of the path), so
$A_i$ is an ovoid. The same for lines. Conversely, ovoids and spreads meet every 2-ball exactly once (§1). $\square$

**Computer-checked 3.3** (research/theorems/polylev/perfcodes.c, triples.py). $H(2)$ has no ovoid and exactly 28
spreads. $H(3)$ has exactly 6,318 spreads and 6,318 ovoids (exact-cover enumeration of the perfect codes of the 2-ball
hypergraph); there are 3,411,720 disjoint pairs of spreads but **no three pairwise disjoint spreads**, so in
particular no partition into 13 spreads, and $k = 13$ is impossible at $q = 3$. (The search for a partition was also
run directly as an exact cover and found none.)

So the extremal case of Corollary 3.1 does not occur at $q = 3$, and near-extremal partitions are rare: dominating sets
only slightly larger than ovoids pack badly. Partitions with $k$ well below $q^2+q+1$ do exist:

**Computer-checked 3.4** (local search, research/theorems/polylev/domlocal.c and translocal.c; every colouring was
re-checked by the independent scorer domcheck.py, which tests every 2-ball).

| $q$ | side | $k$ found | $q^2+q+1$ | method |
|---:|---|---:|---:|---|
DOMTABLE_PLACEHOLDER

**3.5 Group-equivariant colourings.** Let $T=\langle h\rangle$ be a cyclic group of collineations of $H$ of order $d$
acting semiregularly on points and on lines, and fix a representative $b_O$ of every $T$-orbit $O$. Given a block
$a_O\in\{0,\dots,A-1\}$ and a shift $s_O\in\mathbb Z_d$ for every orbit, colour $h^jb_O$ by $a_Od + (j+s_O \bmod d)$.
Then $h$ maps the class of colour $(a,c)$ onto the class $(a,c+1)$ and maps 2-balls to 2-balls, so a 2-ball
$B_2(h^jx)$ sees every colour if and only if $B_2(x)$ does: it suffices to check one 2-ball per orbit, which shrinks
the search by a factor $d$. If the numbers of orbits in the $A$ blocks are the same on the point side and on the line
side (the `fixed` mode of translocal.c), every colour class has as many points as lines, which is the balance condition
of Corollary 3.1; and $\sigma_t$ can be taken $T$-equivariant. We found (g2.py: linear collineations obtained by mapping
the coordinate apartment onto random apartments, products of two of them, powers):

* **Computer-checked 3.6.** Cyclic groups of order $q^2-q+1$ acting semiregularly on the points and lines of $H(q)$
  for $q = 3, 4, 7, 9$ (orders 7, 13, 43, 73; grp/T_q*.h, the $7\times7$ matrices; every line is mapped to a line).
  For $q = 5$ the group of order 21 has line orbits of size 7 (an element of order 3 fixes lines; $3\mid q+1$), so
  only its subgroup of order 7 is semiregular; the same happens for every $q\equiv 2\pmod 3$.
* The Singer cycles of $SL(3,q)\le G_2(q)$, acting by $(v,a,w)\mapsto(gv,a,g^{-T}w)$ in the coordinates
  $x = (v,a,w)$, $v = (x_0,x_1,x_2)$, $a = x_3$, $w = (x_4,x_5,x_6)$, have order $q^2+q+1$; they act semiregularly when
  $q\not\equiv1\pmod 3$ (a fixed point would need an eigenvector of $g$ over $\mathbb F_q$), and their subgroups of
  order prime to 3 act semiregularly for all $q$ (grp/S*_q*.pperm: orders 7 and 13 at $q = 9$, 7 and 19 at $q = 11$, 61
  at $q = 13$, 91 at $q = 16$).

# 4. Diameter 10: a one-sided ball lift and spread stars

For even diameter only one side needs colouring classes.

**Definition 4.1.** Let $I$, $P$, $L$, $N$, $c$ be as in §2, let $\rho'\ge 1$ be odd, and let $L = C_0\cup\dots\cup
C_{K-1}$ be a partition of the lines such that every $C_i$ meets $\{l\in L : d(p,l)\le\rho'\}$ for every point $p$.
Let $r'\ge 1$, $m = 2r'K+1$, and let $\sigma_{t,+},\sigma_{t,-}: P\to L$ ($1\le t\le r'$) be **arbitrary**
bijections. Write $\iota(l) = i$ for $l\in C_i$. The graph $\Lambda'$ has vertex set $(P\cup L)\times\mathbb Z_m$; the
neighbours of $(z,g)$, $z\in P$, are
$$(l,g)\ (l\ni z),\quad (\sigma_{t,+}(z),\ g+(t-1)K+\iota(\sigma_{t,+}(z))+1),\quad
(\sigma_{t,-}(z),\ g-(t-1)K-\iota(\sigma_{t,-}(z))-1)\qquad(1\le t\le r'),$$
and the neighbours of $(l,g)$ are $(p,g)$ ($p\in l$), $(\sigma_{t,+}^{-1}(l), g-(t-1)K-\iota(l)-1)$ and
$(\sigma_{t,-}^{-1}(l), g+(t-1)K+\iota(l)+1)$.

**Theorem 4.2.** $\Lambda'$ is a simple bipartite graph on $2Nm$ vertices, each vertex has degree $\deg_I+2r'$, and
$\operatorname{diam}\Lambda'\le\rho'+c+2$.

*Proof.* The layer changes of the $2r'$ matching edges at a point are pairwise distinct and nonzero modulo $m$ (they lie
in $\pm[(t-1)K+1, tK]$), so $\Lambda'$ is simple; it is bipartite with classes $P\times\mathbb Z_m$, $L\times\mathbb
Z_m$. By the translations it suffices to bound $d((p,0),(l',h))$ for a point $p$ and a line $l'$. If $h = 0$ this is
$\le c$. If $h = -((t-1)K+i+1)$, pick $l\in C_i$ with $d(p,l)\le\rho'$; then
$(p,0)\leadsto(l,0)\to(\sigma_{t,+}^{-1}(l),h)\leadsto(l',h)$ has length $\le\rho'+1+c$. If $h = (t-1)K+i+1$, do the
same with $\sigma_{t,-}$. So every point–line distance is $\le\rho'+c+1$ (odd), and Lemma 2.2(b) gives the claim.
$\square$

**Lemma 4.3 (Theorem).** Let $S$ be a spread of $H(q)$ and, for $s\in S$, let $C_s = B_2(s)$ (the line $s$ and the
lines meeting it). The $C_s$ partition $L$, and every $C_s$ contains a line at distance $\le 3$ from any given point.

*Proof.* The partition is the perfect-code property of spreads (§1). Let $p$ be a point and $s\in S$; $d(p,s)\in\{1,3,5\}$.
If $d(p,s) = 1$, take $s$. If $d(p,s)=3$, the path $p\,m\,x\,s$ gives the line $m\ni p$ meeting $s$, at distance 1. If
$d(p,s) = 5$, the path $p\,m_1\,x_1\,m_2\,x_2\,s$ gives $m_2\in C_s$ at distance 3 from $p$. $\square$

**Corollary 4.4 (Theorem).** For every prime power $q$ and $r'\ge 1$ there is a bipartite $(q+1+2r')$-regular graph of
diameter at most 10 with $2N(q)\,(2r'(q^3+1)+1)$ vertices (Theorem 4.2 with $I = I(q)$, $c = 5$, $\rho' = 3$, and the
classes $C_s$ of a Hermitian spread, $K = q^3+1$).

**Computer-checked 4.5** (squad card r1/c14, research/squads/polylev/r1/c14/build_star.py; apsp.c). The graphs of
Corollary 4.4 with $r' = 1$ and random bijections were built for $q = 2$ (2,394 vertices, degree 5) and $q = 3$
(41,496 vertices, degree 6), two seeds each; all-pairs BFS: bipartite, regular, diameter 8 ($q = 2$) and 9 ($q = 3$),
within the bound 10.

The orders against the lab's current values at $D = 10$ (research/theorems/polylev/sizes.py):

D10TABLE_PLACEHOLDER

None of these beats the lab's Haar graphs; the closest are $(19,10)$ ($q = 16$, 95%) and $(20,10)$ ($q = 17$, 97%).
The reason is visible in the count: the 3-balls of lines that Lemma 4.3 uses have $(q+1)(q^2+1)$ elements, but a class
has to meet all of them and the spread stars have $q^2+q+1$ lines, so $K\le (q+1)(q^2+1)$ while Corollary 4.4 has
$K = q^3+1$; and the sign trick needs two matchings per factor. **Heuristic 4.6:** a partition of the lines into
$K\approx(q+1)(q^2+1)$ classes meeting every set $\{l: d(p,l)\le 3\}$ would roughly add a factor $1+1/q$; it would not
change the conclusion at $D = 10$.

# 5. Diameter 11: disjoint lines and non-collinear points

**Lemma 5.1 (Theorem).** In $H(q)$, (a) the point set of any line meets $B_4(p)$ for every point $p$; (b) the pencil
of any point $z$ (the $q+1$ lines through $z$) meets $B_4(l)$ for every line $l$.

*Proof.* (a) $d(p,\ell)\in\{1,3,5\}$; the point of $\ell$ on the (unique, by (F2)) shortest path from $p$ to $\ell$ is
at distance $d(p,\ell)-1\le 4$ from $p$. (b) is the dual statement: the line through $z$ on the shortest path from $l$
to $z$ is at distance $d(l,z)-1\le 4$ from $l$. $\square$

**Corollary 5.2 (Theorem).** Suppose $H(q)$ has $K$ pairwise disjoint lines $\ell_0,\dots,\ell_{K-1}$ and $K$ pairwise
non-collinear points $z_0,\dots,z_{K-1}$. Then for every $r\ge 1$ there is a bipartite $(q+1+r)$-regular graph of
diameter at most 11 with $2N(q)(2rK+1)$ vertices.

*Proof.* Let $A_i$ be the point set of $\ell_i$ and $B_i$ the pencil of $z_i$ ($|A_i| = |B_i| = q+1$); they are pairwise
disjoint and 4-dominating by Lemma 5.1. Distribute the remaining $N-K(q+1)$ points and lines evenly so that
$|A_i| = |B_i|$ stays true (Remark 2.5) and apply Theorem 2.3 with $\rho = 4$, $c = 5$. $\square$

Pairwise disjoint lines are a partial distance-2 spread and pairwise non-collinear points a partial distance-2 ovoid;
both have at most $q^4+q^2+1 = N/(q+1)$ elements (each point lies on at most one of the lines; each line contains at
most one of the points). Distance-2 ovoids attaining the bound are known only for small $q$ (§9). The sizes, and the
fraction of the bound that $K$ must reach to beat the lab's current values at $(9,11)$ and $(10,11)$:

D11TABLE_PLACEHOLDER

For $\Delta\ge 11$ the lab has no values at $D = 11$ (the 2013 table stops at $D = 10$, and the lab's beyond-table
band covers $D = 11$ only for $\Delta\le 10$).

# 6. Diameter 8, quadrangles and octagons (remarks)

* **$D = 8$.** Theorem 4.2 with $\rho' = 1$ asks for classes of lines meeting every pencil, i.e. sets of lines covering
  every point; there are at most $q+1$ disjoint ones, so $m\le 2r'(q+1)+1$ layers at degree $q+1+2r'$. This is the
  regime of the lab's diameter-8 compound note (research/theorems/D8_COMPOUND.md, branch
  `claude/own-d8-compound-1z4e6s`: about $2q$ layers), and below the 2013 table's pattern at $D = 8$. No new cell.
* **Quadrangles.** For $I$ the incidence graph of a generalized quadrangle of order $(q,q)$ ($c = 3$), Theorem 2.3
  gives diameter $5+\rho$. At $\rho = 2$ ($D = 7$) a class must meet every $p^\perp$ ($q^2+q+1$ points), so
  $k\le q^2+q+1$ and the order is at most $2(q+1)(q^2+1)(2r(q^2+q+1)+1)$. For every $5\le\Delta\le 20$ this bound is
  below the plain hexagon level graph $(2r+1)\cdot 2N(q)$ of the same degree (checked for all prime powers $q\le 19$;
  at $\Delta = 4$ it is 450 against the lab's 864). Mixing hexagon and quadrangle layers does not help in this
  framework: the bound $\rho+c+2$ is set by the largest point–line distance $c$.
* **The Ree–Tits octagon** $GO(q,q^2)$, $q = 2^{2e+1}$, has incidence graph of diameter 8 with point degree $q^2+1$ and
  line degree $q+1$ and $|L|/|P| = (q^2+1)/(q+1)$. Balancing the degrees by duplicating points gives maximum degree
  $\ge q^2+1$: $\Delta = 5$ for $q = 2$ (the incidence graph itself, 4,680 vertices, diameter 8, against the table's
  9,234 at $(5,8)$) and $\Delta\ge 65$ for $q = 8$. Neither falls in a cell the lab tracks ($\Delta\le 20$), so octagons
  give nothing here.
