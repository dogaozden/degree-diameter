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


**Sizes (research/theorems/polylev/sizes.py).** With $k$ at its maximum $q^2+q+1$, and the smallest $k$ that beats the
lab's current value at the same $(\Delta, 9)$ (rows where even the maximum does not are omitted):

| Delta | q | r | max k | order at max k | lab value | k needed to beat it |
|---:|---:|---:|---:|---:|---:|---:|
| 7 | 5 | 1 | 31 | 492,156 | 462,840 | 30 (97%) |
| 9 | 7 | 1 | 57 | 4,509,840 | 3,499,776 | 45 (79%) |
| 10 | 7 | 2 | 57 | 8,980,464 | 8,003,856 | 51 (89%) |
| 10 | 8 | 1 | 73 | 11,010,006 | 8,003,856 | 53 (73%) |
| 11 | 8 | 2 | 73 | 21,945,114 | 16,792,080 | 56 (77%) |
| 11 | 9 | 1 | 91 | 24,313,380 | 16,792,080 | 63 (69%) |
| 12 | 9 | 2 | 91 | 48,493,900 | 34,026,720 | 64 (70%) |
| 13 | 9 | 3 | 91 | 72,674,420 | 67,742,688 | 85 (93%) |
| 13 | 11 | 1 | 133 | 94,601,304 | 67,742,688 | 96 (72%) |
| 14 | 11 | 2 | 133 | 188,848,296 | 116,068,656 | 82 (62%) |
| 15 | 11 | 3 | 133 | 283,095,288 | 208,029,120 | 98 (74%) |
| 15 | 13 | 1 | 183 | 295,239,756 | 208,029,120 | 129 (70%) |
| 16 | 11 | 4 | 133 | 377,342,280 | 337,394,400 | 119 (89%) |
| 16 | 13 | 2 | 183 | 589,675,044 | 337,394,400 | 105 (57%) |
| 17 | 13 | 3 | 183 | 884,110,332 | 501,707,400 | 104 (57%) |
| 18 | 13 | 4 | 183 | 1,178,545,620 | 790,626,816 | 123 (67%) |
| 18 | 16 | 1 | 273 | 1,223,618,214 | 790,626,816 | 177 (65%) |
| 19 | 13 | 5 | 183 | 1,472,980,908 | 1,218,394,320 | 152 (83%) |
| 19 | 16 | 2 | 273 | 2,444,999,466 | 1,218,394,320 | 136 (50%) |
| 19 | 17 | 1 | 307 | 1,855,575,540 | 1,218,394,320 | 202 (66%) |
| 20 | 16 | 3 | 273 | 3,666,380,718 | 1,823,175,864 | 136 (50%) |
| 20 | 17 | 2 | 307 | 3,708,133,884 | 1,823,175,864 | 151 (49%) |

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

| Delta | q | matchings 2r' | K = q^3+1 | order | lab value | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 2 | 2 | 9 | 2,394 | 95,472 | 0.025 |
| 6 | 3 | 2 | 28 | 41,496 | 524,160 | 0.079 |
| 7 | 2 | 4 | 9 | 4,662 | 2,298,240 | 0.002 |
| 7 | 4 | 2 | 65 | 357,630 | 2,298,240 | 0.156 |
| 8 | 3 | 4 | 28 | 82,264 | 8,043,840 | 0.010 |
| 8 | 5 | 2 | 126 | 1,976,436 | 8,043,840 | 0.246 |
| 9 | 2 | 6 | 9 | 6,930 | 23,975,280 | 0.000 |
| 9 | 4 | 4 | 65 | 712,530 | 23,975,280 | 0.030 |
| 10 | 3 | 6 | 28 | 123,032 | 60,141,120 | 0.002 |
| 10 | 5 | 4 | 126 | 3,945,060 | 60,141,120 | 0.066 |
| 10 | 7 | 2 | 344 | 27,019,824 | 60,141,120 | 0.449 |
| 11 | 4 | 6 | 65 | 1,067,430 | 148,729,680 | 0.007 |
| 11 | 8 | 2 | 513 | 76,920,246 | 148,729,680 | 0.517 |
| 12 | 5 | 6 | 126 | 5,913,684 | 325,832,976 | 0.018 |
| 12 | 7 | 4 | 344 | 54,000,432 | 325,832,976 | 0.166 |
| 12 | 9 | 2 | 730 | 194,108,460 | 325,832,976 | 0.596 |
| 13 | 8 | 4 | 513 | 153,765,594 | 677,714,400 | 0.227 |
| 14 | 7 | 6 | 344 | 80,981,040 | 1,326,627,120 | 0.061 |
| 14 | 9 | 4 | 730 | 388,084,060 | 1,326,627,120 | 0.293 |
| 14 | 11 | 2 | 1,332 | 944,241,480 | 1,326,627,120 | 0.712 |
| 15 | 8 | 6 | 513 | 230,610,942 | 2,467,618,800 | 0.093 |
| 16 | 9 | 6 | 730 | 582,059,660 | 4,220,872,800 | 0.138 |
| 16 | 11 | 4 | 1,332 | 1,888,128,648 | 4,220,872,800 | 0.447 |
| 16 | 13 | 2 | 2,198 | 3,537,245,796 | 4,220,872,800 | 0.838 |
| 18 | 11 | 6 | 1,332 | 2,832,015,816 | 11,787,972,672 | 0.240 |
| 18 | 13 | 4 | 2,198 | 7,073,687,124 | 11,787,972,672 | 0.600 |
| 19 | 16 | 2 | 4,097 | 18,331,903,590 | 19,233,722,496 | 0.953 |
| 20 | 13 | 6 | 2,198 | 10,610,128,452 | 30,518,778,360 | 0.348 |
| 20 | 17 | 2 | 4,914 | 29,656,019,484 | 30,518,778,360 | 0.972 |

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

**Lemma 5.4 (Theorem).** (a) Two points of $H(q)$ are at distance $\le 4$ in $I$ if and only if they are
orthogonal with respect to $b$. (b) Every totally singular line $m$ of $Q(6,q)$ (a line of the quadric, not
necessarily a line of $H$) contains a point at distance $\le 4$ from any given point $p$; so the $q+1$ points of $m$ form
a 4-dominating point set.

*Proof.* (a) Points at distance 2 lie on a common line of $H$, which is totally singular; points $x, y$ at distance 4
have a common neighbour point $z$ at distance 2 from both, so both lie in the totally singular plane $\pi_z$. In both
cases $b(x,y) = 0$. Conversely, $p^\perp$ is the tangent hyperplane of $Q(6,q)$ at $p$ (for $q$ even, $p$ is not the
nucleus $\langle e_3\rangle$ of $b$, so $p^\perp$ is still a hyperplane), and $p^\perp\cap Q(6,q)$ is a cone with vertex
$p$ over a parabolic quadric $Q(4,q)$: it has $1+q(q^3+q^2+q+1) = 1+q+q^2+q^3+q^4$ points. The points at distance $\le
4$ from $p$ number $1+q(q+1)+q^3(q+1)$, the same; so the two sets coincide. (b) $m$ is a 2-dimensional subspace and
$p^\perp$ a hyperplane, so they share a nonzero vector, i.e. a point $x$ of $m$ with $b(p,x)=0$; by (a),
$d(p,x)\le 4$. $\square$

**Corollary 5.5 (Theorem).** Suppose $Q(6,q)$ has $K$ pairwise disjoint totally singular lines (a partial line spread
of the quadric) and $H(q)$ has $K$ pairwise non-collinear points. Then the conclusion of Corollary 5.2 holds: for every
$r\ge 1$ there is a bipartite $(q+1+r)$-regular graph of diameter at most 11 with $2N(q)(2rK+1)$ vertices. If $q$ is a
power of 3, the second hypothesis can be dropped: with a duality $\varphi$, the line classes $\varphi(m_i)$ (each a set of
$q+1$ lines of $H$) are 4-dominating (Remark 2.6 and Lemma 5.4(b)), pairwise disjoint and balanced with the point
classes.

*Proof.* As for Corollary 5.2, with Lemma 5.4(b) for the point classes. $\square$

**Computer-checked 5.6.** $Q(6,3)$: a randomized greedy finds 78 pairwise disjoint totally singular lines (85.7% of the
bound 91; qspread.py); with the duality of $H(3)$ (research/d10D7/dual/dualfind.c) both sides have 78 classes, and the
independent scorer domcheck.py confirms that every class meets every 4-ball. The lift with $r = 1$ (lift9.py) has
114,296 vertices; apsp: bipartite, 5-regular, diameter exactly 11 (checks/d11_q3_K78_r1_D11.apsp.txt; the run with
$D = 10$ fails). Squad card r1/c13 built the pencil version at $q = 2$ ($K = 19$, the largest partial distance-2 spread
of $H(2)$, found by exhaustive search): diameter 11 for $r = 1$ and 10 for $r = 2$.

Pairwise disjoint lines are a partial distance-2 spread and pairwise non-collinear points a partial distance-2 ovoid;
both have at most $q^4+q^2+1 = N/(q+1)$ elements (each point lies on at most one of the lines; each line contains at
most one of the points). Distance-2 ovoids attaining the bound are known only for small $q$ (§9). The sizes, and the
fraction of the bound that $K$ must reach to beat the lab's current values at $(9,11)$ and $(10,11)$:

| Delta | q | r | max K | order at max K | lab value | K needed to beat it |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 2 | 1 | 21 | 5,418 | 19,152 | impossible |
| 5 | 2 | 2 | 21 | 10,710 | 253,080 | impossible |
| 5 | 3 | 1 | 91 | 133,224 | 253,080 | impossible |
| 6 | 2 | 3 | 21 | 16,002 | 1,971,744 | impossible |
| 6 | 3 | 2 | 91 | 265,720 | 1,971,744 | impossible |
| 6 | 4 | 1 | 273 | 1,493,310 | 1,971,744 | impossible |
| 7 | 2 | 4 | 21 | 21,294 | 10,648,176 | impossible |
| 7 | 3 | 3 | 91 | 398,216 | 10,648,176 | impossible |
| 7 | 4 | 2 | 273 | 2,983,890 | 10,648,176 | impossible |
| 7 | 5 | 1 | 651 | 10,179,036 | 10,648,176 | impossible |
| 8 | 2 | 5 | 21 | 26,586 | 43,702,560 | impossible |
| 8 | 3 | 4 | 91 | 530,712 | 43,702,560 | impossible |
| 8 | 4 | 3 | 273 | 4,474,470 | 43,702,560 | impossible |
| 8 | 5 | 2 | 651 | 20,350,260 | 43,702,560 | impossible |
| 9 | 2 | 6 | 21 | 31,878 | 145,258,344 | impossible |
| 9 | 3 | 5 | 91 | 663,208 | 145,258,344 | impossible |
| 9 | 4 | 4 | 273 | 5,965,050 | 145,258,344 | impossible |
| 9 | 5 | 3 | 651 | 30,521,484 | 145,258,344 | impossible |
| 9 | 7 | 1 | 2,451 | 192,276,048 | 145,258,344 | 1852 (76%) |
| 10 | 2 | 7 | 21 | 37,170 | 445,709,568 | impossible |
| 10 | 3 | 6 | 91 | 795,704 | 445,709,568 | impossible |
| 10 | 4 | 5 | 273 | 7,455,630 | 445,709,568 | impossible |
| 10 | 5 | 4 | 651 | 40,692,708 | 445,709,568 | impossible |
| 10 | 7 | 2 | 2,451 | 384,512,880 | 445,709,568 | impossible |
| 10 | 8 | 1 | 4,161 | 623,376,054 | 445,709,568 | 2975 (71%) |
| 11 | 9 | 1 | 6,643 | 1,765,310,820 | - | - |
| 12 | 9 | 2 | 6,643 | 3,530,488,780 | - | - |
| 13 | 11 | 1 | 14,763 | 10,461,770,424 | - | - |
| 14 | 11 | 2 | 14,763 | 20,923,186,536 | - | - |
| 15 | 13 | 1 | 28,731 | 46,227,144,684 | - | - |
| 16 | 13 | 2 | 28,731 | 92,453,484,900 | - | - |
| 17 | 13 | 3 | 28,731 | 138,679,825,116 | - | - |
| 18 | 16 | 1 | 65,793 | 294,355,118,694 | - | - |
| 19 | 16 | 2 | 65,793 | 588,708,000,426 | - | - |
| 20 | 17 | 2 | 83,811 | 1,011,499,873,020 | - | - |

(Rows with "-": no lab value; the row shown is the largest order at that degree, at the upper bound for $K$.)

**Computer-checked 5.3** (squad cards r1/c11, r1/c12; sets re-checked against the hexagon files). $H(7)$ has 1,619
pairwise disjoint lines and 1,618 pairwise non-collinear points (iterated local search, research/gh6/ils_mis.c), so
$K\ge 1{,}618$ at $q = 7$ (66% of the bound; 1,852 would be needed at $(9,11)$). $H(8)$ has 2,701 pairwise disjoint lines
and 2,701 pairwise non-collinear points, each a union of 37 orbits of the Singer subgroup of order 73 of $SL(3,8)$
(local search on the orbit quotient), so $K\ge 2{,}701$ at $q = 8$ (65%; 2,975 would be needed at $(10,11)$).

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

# 7. Where this leaves diameters 8–10

* **$D = 8$.** No construction here reaches the lab's values or the 2013 table. The table's $D=8$ entries are Gómez's
  compounds $\Omega H_q$, which the lab found not to have diameter 8 as published (papers/Ozden_OmegaH_D8_note.pdf);
  the lab's own compound note gets about $2q$ layers, and §6 gives at most $2r'(q+1)+1$.
* **$D = 9$.** Corollary 3.1 is the first construction in this family whose order grows like
  $4rq^2\cdot q^5$: with $k$ at its maximum $q^2+q+1$ it would beat the lab's value at $D = 9$ for every
  $7\le\Delta\le 20$ except $\Delta = 8$ (table in §3). The obstacle is the size of $k$ that can actually be realised
  (Computer-checked 3.3, 3.4): perfect partitions do not exist at $q = 3$, Hermitian spreads of $H(9)$ pairwise
  intersect (Computer-checked 7.1), and the local searches reached only about half of the maximum. The record thresholds
  need $k/(q^2+q+1)$ between 49% ($(20,9)$, $q = 17$) and 97%.
* **$D = 10$.** Corollary 4.4 holds for every $q$ with no search at all; it reaches 84–97% of the lab's Haar values at
  $(16,10)$, $(19,10)$, $(20,10)$ and beats none.
* **$\Delta\ge 17$.** The beyond-table cells at $D = 8$–$10$ hold Haar graphs at 4.5–7% of the Moore bound; the ball
  lifts reach that range only at $D = 9$ with large $k$ (e.g. $(19,9)$ and $(20,9)$ need $k\ge 136$ at $q = 16$, half the
  maximum 273).

**Computer-checked 7.1** (squad card r1/c02, research/squads/polylev/r1/c02/). In $H(9)$, 5,000 Hermitian spreads (lines
of $H(9)$ in a hyperplane $v^\perp$ with $q^3+1$ lines of $H$) were sampled; every one of the 12,497,500 pairs meets, in
1 line (22.0%) or 10 lines (78.0%). One fixed Hermitian spread was compared with the line sets of all 597,871
hyperplanes of $PG(6,9)$: the intersections have 1, 10 or 730 lines, never 0. Since $G_2(9)$ acts transitively on
the elliptic hyperplanes (**Heuristic**: we did not check this transitivity by computer), no two Hermitian spreads of
$H(9)$ are disjoint, and by Remark 2.6 the same holds for the Hermitian ovoids.

# 8. Computer checks

All files are under research/theorems/polylev/ unless stated otherwise; `hexgen2` is research/d10D7/hexgen2.c (the lab's
generator of $H(q)$, which checks $N$ points, $N$ lines, $q+1$ points per line and lines per point), and `apsp` is
research/lifts/coordinator_check/apsp.c (all-pairs bit-parallel BFS: simple, maximum degree, bipartite, connected,
exact diameter; it assumes no symmetry).

| claim | check | result |
|---|---|---|
| Theorem 2.3 / Cor. 3.1, $q = 3$, $k = 7$ | lift9.py + apsp, $r = 1, 2, 3$ (10,920; 21,112; 31,304 vertices) | bipartite, regular of degree $q+1+r$; diameter 9, 9, 8; "$D = 8$" fails for $r = 1, 2$ |
| Cor. 3.1, $q = 4$, $k = 13$ | squad r1/c13: translocal colourings, lift9.py, apsp (73,710; 144,690 vertices) | diameter $\le 9$ for $r = 1, 2$; "$D = 8$" fails |
| Cor. 4.4, $q = 2, 3$, $r' = 1$ | squad r1/c14: build_star.py + apsp (2,394; 41,496 vertices, 2 seeds each) | diameter 8 ($q=2$), 9 ($q=3$) |
| Cor. 5.2 | CHECK511_PLACEHOLDER | |
| Comp. 3.3 | perfcodes.c (exact cover), triples.py | 28 spreads, no ovoid in $H(2)$; 6,318 spreads and 6,318 ovoids in $H(3)$; no 3 pairwise disjoint spreads |
| Comp. 3.4 | domlocal.c, translocal.c; independent scorer domcheck.py (tests every 2-ball by BFS) | see the table in §3 |
| Comp. 3.6 | g2.py (collineations by apartment maps, verified on all lines), singer_perms.py (orbit sizes printed) | semiregular groups listed in §3.5 |
| Comp. 5.3 | squad r1/c11, r1/c12 (ils_mis.c, mis2.c; sets re-verified) | $K\ge 1{,}618$ ($q=7$), $K\ge 2{,}701$ ($q=8$) |
| Comp. 7.1 | squad r1/c02 (sample.py, full_check.py) | Hermitian spreads of $H(9)$ pairwise meet |

The squad runs, their scoreboard and their logs are in research/squads/polylev/r1/ (log of the rounds in
research/squads/LOG.md).

# 9. Prior art

Searches by squad card r1/c16 (research/squads/polylev/r1/c16/prior_art.md, with evidence tags) and the lab's
novelty file (research/lit/novelty-2026-10-25.md on branch `claude/novelty-literature-check-4i5frp`).

* **Level graphs ($\rho = 0$).** The $D = n+1$ level graphs of generalized polygons with a tournament of layers are the
  Gómez–Fiol compounds $B(T)$ (J. Gómez, M. A. Fiol, *Dense compound graphs*, Ars Combin. 20-A (1985)) and give the
  2013 table's diameter-7 column, credited to Delorme, Gómez and Quisquater (*On large bipartite graphs*, cited as
  submitted; not found). Remark 2.4 is that construction.
* **Voltage lifts of polygon incidence graphs at larger diameter.** C. Delorme, *Grands graphes de degré et diamètre
  donnés*, European J. Combin. 6 (1985) 291–302, §4: products $G*\Gamma'$ of the incidence graph $G$ of a generalized
  quadrangle or hexagon with an oriented perfect matching; item (c), $G*C_{35}$, has degree $\Delta+2$, diameter
  $D+3$ and $35n$ vertices, i.e. for $H(q)$ degree $q+3$, diameter 9 and $70N(q)$ vertices (card c16 read the full text;
  bipartiteness of (c) is not stated there; the bipartite versions are in C. Delorme, *Large bipartite graphs with given
  degree and diameter*, J. Graph Theory 9 (1985) 325–334, not read). This is the closest prior construction to
  Corollary 3.1, which has $2N(4k+1)$ vertices at the same degree and diameter, more than $70N$ as soon as $k\ge 9$.
  Delorme's layers are indexed by a fixed cyclic group and every jump has a fixed voltage per arc; the ball lift lets the
  voltage depend on the colour class of the jumping element, which is what makes the number of layers grow like $q^2$.
* **Hubs and freed sets** (D7 note; R. Rajiv, Zenodo 2026, doi 10.5281/zenodo.23052995) concern diameter $n$ and
  $n+1$; not used here.
* **Ovoids, spreads, partitions.** Thas (J. Combin. Theory Ser. A 29 (1980)) relates ovoids of $H(q)$ to perfect codes
  (not read). Distance-2 ovoids of $H(q)$ are known only for $q = 2, 3, 4$ (De Wispelaere–Van Maldeghem 2008, cited by
  Bishnoi–Ihringer, arXiv:1606.07288). For partitions of the points of $H(q)$ into ovoids, of its lines into spreads, or
  the domatic number of its collinearity graph: nothing found in these sources.
* **Bipartite values at $D = 9$, $D = 11$ after 2013:** nothing found in these sources (the CombinatoricsWiki page could
  not be retrieved on 28 October 2026).
