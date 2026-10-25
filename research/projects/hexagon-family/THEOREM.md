# Bipartite graphs of diameter 7 from generalized hexagons, with freed points

Project hexagon-family, 2026-10-25. Draft; the computer-checked instances are listed in §7 and the Lean status in §8.

## Abstract

Let $n_b(\Delta,7)$ be the largest order of a bipartite graph with maximum degree $\Delta$ and diameter 7. For a
generalized hexagon $\mathcal H$ of order $(q,q)$ with $N=(q+1)(q^4+q^2+1)$ points and $N$ lines, $2j+1$ copies of its
incidence graph joined by $j$ shifted copies of one bijection $\sigma$ (points $\to$ lines) give a
$(q+1+j)$-regular bipartite graph of diameter 7 and order $2(2j+1)N$; these are the table values of the D = 7
column. We show that every point $r$ of a set $R$ can be *freed* (its $j(2j+1)$ extra edges removed and replaced by
$2j$ new vertices) as long as

1. no two points of $R$ are collinear, and
2. $\sigma$ is a *local duality* at every $r\in R$: $\sigma$ maps the $q(q+1)$ points collinear with $r$ onto the
   $q(q+1)$ lines concurrent with $\sigma(r)$,

and the new vertices are joined by a small bipartite graph whose same-side distances are at most 6. This gives

$$n_b(q+1+j,\,7)\ \ge\ 2(2j+1)(q+1)(q^4+q^2+1)+2j\,|R| .$$

Condition 2 can be met for $R$ pairwise opposite (a partial ovoid of $Q(6,q)$ when $\mathcal H=H(q)$), and for any
$R$ satisfying 1 when $\mathcal H$ has a duality ($H(q)$, $q=3^h$). We characterise condition 2 combinatorially
(Lemma 3: the "midpoint structure" of $R$ must occur among the lines too) and bound $|R|$: $|R|\le q^4+q^2+1$
always, and $|R|\le q^3+1$ for pairwise opposite sets, with $|R|\le q^3$ when $H(q)$ has no ovoid. Lemma 3 also
lets a maximal pairwise opposite set be extended by points at distance 4 from some of its points (Proposition 4), a
cell-counting criterion that is easy to search; this raised every table cell with a pure record set that we tried
(§7).

## 1. Setting

A *generalized hexagon of order $(q,q)$* ($q\ge2$) is a point–line geometry whose incidence graph $I$ is bipartite,
$(q+1)$-regular, of diameter 6 and girth 12. Write $d$ for the distance in $I$, $P$ and $L$ for the points and lines,
$\Gamma_k(x)=\{y: d(x,y)=k\}$. Points $x,y$ are *collinear* if $d(x,y)=2$, *opposite* if $d(x,y)=6$; lines are
*concurrent* if at distance 2. Point–line distances are odd, so at most 5; point–point and line–line distances are
even, at most 6. $|P|=|L|=N=(q+1)(q^4+q^2+1)$, $|\Gamma_2(x)|=q(q+1)$ for every element $x$.

The split Cayley hexagon $H(q)$ (Tits) has as points all points of the parabolic quadric
$Q(6,q):\ x_0x_4+x_1x_5+x_2x_6=x_3^2$, and two points are at distance $\le4$ iff they are orthogonal for the polar
form $B$; so a set of pairwise opposite points of $H(q)$ is exactly a partial ovoid of $Q(6,q)$. $H(q)$ is self-dual
iff $q=3^h$.

Only two facts about $I$ are used in the proofs below, and both hold in every generalized hexagon:

**(F1)** every point–line distance is at most 5 and every point–point and line–line distance at most 6;
**(F2)** every point is on at least two lines and every line has at least two points.

**Covering lemma.** For every line $\ell$ and point $x$ there is a line $\ell'\in\Gamma_2(\ell)$ with
$d(\ell',x)\le3$. Dually, for every point $p$ and line $m$ some $p'\in\Gamma_2(p)$ has $d(p',m)\le3$.

*Proof.* $d(\ell,x)\in\{1,3,5\}$ by (F1). If it is 3 or 5, the second line $\ell'$ of a shortest path
$\ell,y,\ell',\dots,x$ meets $\ell$ in $y$ and $\ell'\neq\ell$ (the path is shortest), so $\ell'\in\Gamma_2(\ell)$ and
$d(\ell',x)=d(\ell,x)-2\le3$. If $x\in\ell$, take any other line $\ell'$ through $x$ (F2); $d(\ell',x)=1$. $\square$

## 2. The construction $X_j(\mathcal H,\sigma,R,\mathcal N)$

Fix $j\ge1$, $m=2j+1$, a bijection $\sigma:P\to L$ and a set $R\subseteq P$. Vertices:

- $(x,i)$ for $x\in P\cup L$, $i\in\mathbb Z_m$ (the *levels*);
- *hubs*: a set $V$ of line-type hubs and a set $U$ of point-type hubs, each hub with an *owner* in $R$, every
  $r\in R$ owning at most $j$ hubs of each type.

Edges:

- $(p,i)\sim(\ell,i)$ when $p\in\ell$ (every level);
- $(p,i)\sim(\sigma(p),i+k)$ for $k=1,\dots,j$, every $i$, every $p\notin R$ (the *shift edges*);
- a hub $v\in V$ with owner $r$ is joined to $(r,i)$ for all $i$; a hub $u\in U$ with owner $r$ to
  $(\sigma(r),i)$ for all $i$;
- a bipartite *hub graph* $\mathcal N$ between $V$ and $U$.

So $R$ is the set of *freed* points: $(r,i)$ and $(\sigma(r),i)$ lose their $j$ shift edges and get up to $j$ hubs
instead. With $R=\emptyset$ this is the table construction ($m=3$: Delorme–Gómez–Quisquater's $3|I|$; $m=5,7$: the
$(q+3,7)$ and $(q+4,7)$ values).

**Bipartite and degrees.** Points and point-type hubs form one side, lines and line-type hubs the other. A point
$(p,i)$ with $p\notin R$ has degree $(q+1)+j$; a line $(\ell,i)$ with $\ell\notin\sigma(R)$ also ($j$ shift edges
from $(\sigma^{-1}\ell,i-k)$); $(r,i)$ and $(\sigma(r),i)$ have degree $q+1$ plus their hubs, at most $q+1+j$; a hub
has degree $m+\deg_{\mathcal N}$. So the maximum degree is at most $q+1+j$ iff every hub has degree at most $q-j$
in $\mathcal N$.

**Order.** $2mN+|V|+|U|$, at most $2mN+2j|R|$.

## 3. The theorem

**Theorem 1.** Let $\mathcal H$ be a generalized hexagon of order $(q,q)$ and suppose

- **(R1)** no two points of $R$ are collinear;
- **(R2)** $\sigma(\Gamma_2(r))=\Gamma_2(\sigma(r))$ for every $r\in R$;
- **(R3)** any two hubs of the same type whose owners are opposite are at distance at most 6 in $\mathcal N$.

Then $X_j(\mathcal H,\sigma,R,\mathcal N)$ has diameter at most 7.

Two consequences of (R1)–(R2) are used:

**(C1)** $\sigma(R)$ has no two concurrent lines: if $\sigma(s)\in\Gamma_2(\sigma(r))=\sigma(\Gamma_2(r))$ then
$s\in\Gamma_2(r)$, against (R1). In particular every point lies on at most one line of $\sigma(R)$.

**(C2)** $d(\sigma(r),\sigma(s))=d(r,s)$ for $r,s\in R$: if $d(r,s)=4$ with midpoint $z$ then
$\sigma(z)\in\Gamma_2(\sigma r)\cap\Gamma_2(\sigma s)$, so $d(\sigma r,\sigma s)\le4$, and it is not $0$ or $2$ by
(C1); if $d(\sigma r,\sigma s)=4$ with midline $w$ then $\sigma^{-1}(w)\in\Gamma_2(r)\cap\Gamma_2(s)$ and $d(r,s)=4$.

*Proof of Theorem 1.* Inside one level the hexagon is untouched, so distances are at most 6. Two different levels
differ by $\pm k$ with $1\le k\le j$ ($m$ is odd), so take $(x,i)$ and $(y,i+k)$ with $1\le k\le j$.

1. *$x=a$ a point, $a\notin R$:* $(a,i)\to(\sigma a,i+k)\leadsto(y,i+k)$, length $\le1+6=7$.
2. *$x=a$ a line, $y=b$ a point:* by (C1) and (F2) some line $w\ni b$ is not in $\sigma(R)$, so
   $\sigma^{-1}(w)\notin R$; $(a,i)\leadsto(\sigma^{-1}w,i)\to(w,i+k)\to(b,i+k)$, length $\le5+1+1=7$.
3. *$x=a$ a line, $y=b$ a line, $b\notin\sigma(R)$:* $(a,i)\leadsto(\sigma^{-1}b,i)\to(b,i+k)$, length $\le5+1=6$.
4. *$x=r\in R$, $y=b$ a point:* by (R2) the lines $\sigma(p')$, $p'\in\Gamma_2(r)$, are the lines of
   $\Gamma_2(\sigma r)$, so by the covering lemma one of them has $d(\sigma p',b)\le3$. The points $p'$ are not in
   $R$ (R1), so $(p',i)\sim(\sigma p',i+k)$ is an edge: $(r,i)\leadsto(p',i)\to(\sigma p',i+k)\leadsto(b,i+k)$,
   length $\le2+1+3=6$.
5. *$x=r\in R$, $y=b$ a line:* pick $w\in\Gamma_2(\sigma r)$ with $d(w,b)\le4$: the third vertex of a shortest
   path from $\sigma(r)$ to $b$ if $d(\sigma r,b)\ge2$ (F1 gives $d\le6$), any $w\in\Gamma_2(\sigma r)$ if
   $b=\sigma(r)$. By (R2) $p'=\sigma^{-1}(w)\in\Gamma_2(r)$, not in $R$:
   $(r,i)\leadsto(p',i)\to(w,i+k)\leadsto(b,i+k)$, length $\le2+1+4=7$.
6. *$x=a$ a line, $y=\sigma(r)$, $r\in R$:* dual of 4. By (R2) the points $\sigma^{-1}(w)$,
   $w\in\Gamma_2(\sigma r)$, are the points of $\Gamma_2(r)$, none in $R$; by the dual covering lemma one of them has
   $d(\sigma^{-1}w,a)\le3$, and $(\sigma^{-1}w,i)\sim(w,i+k)$:
   $(\sigma r,i+k)\leadsto(w,i+k)\to(\sigma^{-1}w,i)\leadsto(a,i)$, length $\le2+1+3=6$.

Cases 1–6 cover every pair (a point $x$ is in $R$ or not; for a line $x$, $y$ is a point, a line outside
$\sigma(R)$, or a line of $\sigma(R)$). Hubs: a hub $v$ with owner $r$ reaches $(y,i)$ through $(r,i)$ in
$1+d(r,y)\le7$, and a hub $u$ with owner $r$ through $(\sigma r,i)$ likewise. Two hubs $v,u$ of different types:
$v\to(r,i)\leadsto(\sigma s,i)\to u$, length $\le2+5=7$. Two hubs of the same type with owners $r,s$: distance 2 if
$r=s$; $\le1+4+1=6$ through one level if $d(r,s)=4$ (for $U$-hubs use (C2)); $\le6$ by (R3) if $r,s$ are opposite.
These are all cases ($d(r,s)\ne2$ by (R1)). $\square$

**Remarks.** (a) No hub is needed for the freed vertices themselves (cases 4–6 avoid them); hubs only use the freed
degree. (b) Only (F1), (F2) and (R1)–(R3) are used, not the girth. (c) If two points of $R$ were collinear, case 4
would lose the route through the other one, and the covering in case 4 is exact (for $b$ at distance 5 from
$\sigma(r)$ exactly one line of $\Gamma_2(\sigma r)$ is within 3 of $b$), so (R1) cannot simply be dropped.

## 4. When does a local duality exist?

**Lemma 2 (pairwise opposite sets).** If $R\subseteq P$ is pairwise opposite, $S\subseteq L$ is pairwise opposite and
$|S|=|R|$, then for every bijection $\tau:R\to S$ there is a bijection $\sigma:P\to L$ extending $\tau$ that satisfies
(R2).

*Proof.* The sets $\{r\}\cup\Gamma_2(r)$, $r\in R$, are pairwise disjoint (two of them meeting would put two points
of $R$ at distance $\le4$), and so are the $\{s\}\cup\Gamma_2(s)$, $s\in S$. Map $r\mapsto\tau(r)$, map
$\Gamma_2(r)$ bijectively onto $\Gamma_2(\tau r)$ (both have $q(q+1)$ elements), and the remaining
$N-|R|(1+q(q+1))$ points bijectively onto the remaining lines (same number). $\square$

For $H(q)$, $S$ can be taken from the Hermitian spread: the $q^3+1$ lines of $H(q)$ contained in a hyperplane
$\Pi$ with $\Pi\cap Q(6,q)=Q^-(5,q)$ are pairwise opposite. So for $H(q)$ the only constraint is on the points:
**$R$ any partial ovoid of $Q(6,q)$ with $|R|\le q^3+1$.**

**Corollary (duality).** If $\mathcal H$ has a duality $\delta$ (a bijection $P\cup L\to L\cup P$ preserving
incidence) then $\sigma=\delta|_P$ satisfies (R2) at every point, so **every set $R$ with (R1)** can be freed. This
is the case $H(q)$, $q=3^h$.

**Lemma 3 (what (R2) means in general).** For $R$ with (R1) and $S=\sigma(R)$, call $z\in P$ a *midpoint* of $R$ if
it is collinear with at least two points of $R$ (then $d(r,s)=4$ for any two of them, and $z$ is their unique
midpoint), and define midlines of $S$ dually. A bijection $\tau:R\to S$ extends to some $\sigma$ with (R2) iff

- $d(\tau r,\tau s)=d(r,s)$ for all $r,s\in R$ (so in $\{4,6\}$), and
- there is a bijection $\mu$ from the midpoints of $R$ to the midlines of $S$ with $\tau(\Gamma_2(z)\cap R)=
  \Gamma_2(\mu z)\cap S$ for every midpoint $z$.

*Proof.* Necessity: $\mu=\sigma|$ (C2 and the argument in it). Sufficiency: for $r\in R$, $\Gamma_2(r)$ contains the
midpoints $z$ with $r\in\Gamma_2(z)$, and $\Gamma_2(\tau r)$ the midlines $\mu(z)$ for the same $z$; map these by
$\mu$ and the rest of $\Gamma_2(r)$ (non-midpoints, which lie in no other $\Gamma_2(s)$) bijectively onto the rest of
$\Gamma_2(\tau r)$; the remaining points onto the remaining lines. $\square$

So in general (R1)–(R2) ask for a configuration "$R$ together with its midpoints" that occurs both among the points
of $\mathcal H$ and among the lines of $\mathcal H$ (the points of the dual hexagon). Pairwise opposite sets have no
midpoints and occur on both sides trivially; with a duality every configuration does. For $H(q)$, $q\ne3^h$, the
dense configurations are rigid on the point side ($\Gamma_2(r)\cup\{r\}$ is a plane of $Q(6,q)$, the points
$z\in\Gamma_2(r)$ at distance 4 from a point opposite $r$ form a line of that plane) and the line side of $H(q)$ does
not have this regularity, so only sparse midpoint structures transfer. Experiment (§7.3): random greedy pairs
$(R,S)$ built under Lemma 3 reach $|R|=20,29,39$ for $q=3,4,5$, against $16,21,30$ for pairwise opposite greedy;
both stay far below the structured partial ovoids (72 at $q=5$).

**Proposition 4 (extending a pairwise opposite set by points with midpoints).** Let $R$ be a pairwise opposite
set of points, $\mathrm{Sp}$ a pairwise opposite set of lines with $|\mathrm{Sp}|\ge|R|$, and let
$x_1,\dots,x_t$ be pairwise opposite points, none collinear with a point of $R$, and $s_1,\dots,s_t$ pairwise
opposite lines not in $\mathrm{Sp}$. Each $s_i$ meets at most one line $\ell_i$ of $\mathrm{Sp}$ (two would be at
distance $\le4$ from each other). For $r\in R$ put $T(r)=\{i: d(r,x_i)=4\}$, and for
$\ell\in\mathrm{Sp}':=\mathrm{Sp}\setminus\{\ell_1,\dots,\ell_t\}$ put $T(\ell)=\{i: d(\ell,s_i)=4\}$. If
$$\#\{r\in R: T(r)=T\}\ \le\ \#\{\ell\in\mathrm{Sp}': T(\ell)=T\}\qquad\text{for every }T\subseteq\{1,\dots,t\},$$
then $R\cup\{x_1,\dots,x_t\}$ satisfies (R1) and, with a suitable $S\subseteq\mathrm{Sp}'$ and $\tau$, the
conditions of Lemma 3; so all $|R|+t$ points can be freed.

*Proof.* Choose $\tau$ cell by cell: it maps the points of $R$ with pattern $T$ injectively to lines of
$\mathrm{Sp}'$ with pattern $T$, and $\tau(x_i)=s_i$. (R1): $x_i$ is not collinear with $R$, and two $x$'s are
opposite. Distances: inside $R$, inside $X$, inside $\tau(R)$ and among the $s_i$ all are 6. For $r\in R$,
$d(r,x_i)\in\{4,6\}$ and it is 4 iff $i\in T(r)$; for $\ell=\tau(r)$, $d(\ell,s_i)\ne2$ because $\ell\ne\ell_i$, so
it is 4 iff $i\in T(\ell)=T(r)$. Midpoints: a point collinear with two points of $R\cup X$ is collinear with exactly
one $r$ and one $x_i$ (two points of $R$, or two of $X$, collinear with it would be at distance $\le4$), so it is
the midpoint of exactly one pair $(r,x_i)$; dually each midline of $\tau(R)\cup\{s_i\}$ belongs to exactly one pair
$(\tau r,s_i)$. So $\mu$: midpoint of $(r,x_i)$ $\mapsto$ midline of $(\tau r,s_i)$ is a well defined bijection, and
Lemma 3 applies. $\square$

The counting condition is cheap to test, so a greedy (`ext/extend2.py`) adds points $x$ with few distance-4
neighbours in $R$, trying random lines $s$. Every point outside the record sets is at distance 4 from at least
11 ($q=5$), 30 ($q=7$), 60 ($q=11$), 24 ($q=13$) of their points, and each $s$ is at distance 4 from about $q^2$
spread lines, so the cells stay populated for a while; see §7 for what it gives.

## 5. Bounds on $|R|$

**Proposition 5.** Under (R1), $|R|\le q^4+q^2+1$, with equality iff $R$ meets every line in exactly one point (a
distance-2 ovoid). Under (C1) the same holds for $\sigma(R)$ (a partial distance-2 spread). So
$$|R|\le\min\{\text{max partial distance-2 ovoid of }\mathcal H,\ \text{max partial distance-2 spread of }\mathcal H\}.$$

*Proof.* Each line contains at most one point of $R$ and each point lies on $q+1$ lines:
$(q+1)|R|\le|L|=(q+1)(q^4+q^2+1)$. $\square$

For $H(q)$ distance-2 ovoids are known only for $q=2,3,4$, and the dual $H(q)^D$ has none for $q=2,4$
(Bishnoi–Ihringer), i.e. $H(2)$ and $H(4)$ have no distance-2 spread; so equality fails for $q=2,4$.

**Proposition 6 (pairwise opposite).** For $H(q)$, a pairwise opposite set has at most $q^3+1$ points, with equality
iff it is an ovoid of $Q(6,q)$.

*Proof.* The generators (totally singular planes) of $Q(6,q)$ are $(q+1)(q^2+1)(q^3+1)$ in number, each point lies on
$(q+1)(q^2+1)$ of them, and a plane contains at most one point of $R$ (its points are pairwise orthogonal). Count
incidences. $\square$

Ovoids of $Q(6,q)$ exist for $q=3^h$ (Thas; Kantor) and do not exist for $q$ even (Thas) or $q$ prime $>3$ (Ball,
Govaerts, Storme 2006) [literature; not re-proved here]. So for the cells of the table:

| cell(s) | $q$ | levels | bound used | best known $|R|$ | $n$ with the best $R$ |
|---|---|---|---|---|---|
| (7,7) | 5 | 3 | pairwise opposite, $\le125$ | 72 | 23,580 |
| (9,7) | 7 | 3 | $\le343$ | 288 | 118,224 |
| (10,7) | 8 | 3 | $\le512$ | 217 | 225,128 |
| (11,7) | 9 | 3 | duality: (R1), $\le6643$ | 4,291 | 407,162 |
| (12,7) | 9 | 5 | (R1), $\le6643$; hubs limited by $\mathcal N$ | 4,291 (3,942 hubs used) | 680,068 |
| (13,7), (14,7), (15,7) | 11 | 3, 5, 7 | $\le1331$ | 756 | 1,064,448; 1,774,584; 2,484,720 |
| (16,7) | 13 | 5 | $\le2197$ | 792 | 4,025,508 |

(The numbers in the last two columns are the records at the start of this project; see §7 for changes.)

**The hub graph is not a bound in principle.** (R3) asks for a bipartite graph on $j|R|$ + $j|R|$ vertices, maximum
degree $q-j$, same-side distances $\le6$. Its order per side can be as large as
$1+d(d-1)+d(d-1)^3+d(d-1)^5$, $d=q-j$, far above $j(q^4+q^2+1)$ for $q\ge5$. In practice it needs a construction once
$j|R|$ is a sizeable fraction of that: for (12,7) ($d=7$) the record used a 2-level cover of $H(5)$ with 7,884
vertices per side, while 8,582 hubs per side would be allowed by $R$.

## 6. Summary of what the construction needs

Freeing a point $r$ requires exactly: the routes of Theorem 1 cases 4–6 (or others) from $(r,i)$ to the points of
level $i+k$ opposite $r$, and from $(\sigma r,i+k)$ to the lines of level $i$ opposite $\sigma(r)$. The local
duality (R2) is the clean sufficient condition; with it, (R1) is necessary (Remark c). Within (R1)–(R2):

- with a duality ($q=3^h$): any partial distance-2 ovoid, $|R|\le q^4+q^2+1$;
- pairwise opposite: any partial ovoid of $Q(6,q)$, $|R|\le q^3+1$ ($\le q^3$ for $q$ even or prime $>3$);
- mixed (midpoints allowed, Lemma 3): between the two. Proposition 4 extends every record pairwise opposite set we
  tried by a few per cent of points at distance 4 (§7): so the bound $q^3+1$ is not a bound for what the
  construction needs. We know no better upper bound than $q^4+q^2+1$ for mixed sets without a duality; the largest
  we found are still below $q^3+1$.

## 7. Instances and checks

All graphs below were rebuilt from their solution files and checked by an all-pairs BFS
(research/lifts/coordinator_check/apsp_mt.c, no symmetry assumed); the checker prints the exact diameter.

| cell | $q$ | $j$ | freed set | hubs per side | $n$ | check |
|---|---|---|---|---|---|---|
| (7,7) | 5 | 1 | 72 pairwise opposite + 9 mixed (Prop. 4) | 81 | **23,598** | diameter 7 |
| (9,7) | 7 | 1 | 288 + 8 mixed | 296 | **118,240** | diameter 7 |
| (10,7) | 8 | 1 | 217 + 15 mixed | 232 | **225,158** | diameter 7 |
| (11,7) | 9 | 1 | 4,306 non-collinear points, $\sigma$ = duality | 4,306 (random degree-8 hub graph) | **407,192** | diameter 7, 11-regular |
| (12,7) | 9 | 2 | the same 4,306 points | 8,580 (Haar graph of PSL(2,11)×Z13, Δ 7, D 7) | **681,460** | diameter 7 |
| (13,7) | 11 | 1 | 756 + 12 mixed | 768 | **1,064,472** | diameter 7 (apsp_orb) |

In progress at the time of writing (see HANDOFF.md for the final state): $q=11$ with 756 + 14 = 770 (round 3, c3:
all lines scanned) for (13,7), (14,7), (15,7); $q=13$ with 792 + 24 = 816 (round 3, c4) for (16,7).

**$q=16$** (not a table cell: $\Delta=q+2=18$): an elliptic quadric $Q^-(3,16)$ in a 4-space gives 257 pairwise
opposite points (sets/P16_ell257.txt); random greedy gives at most 180 (4 runs); so
$n_b(18,7)\ge6\cdot17\cdot65{,}793+2\cdot257=6{,}711{,}400$ by Theorem 1 with Lemma 2 and the Hermitian spread (graph not built).

Earlier records of this family (pairwise opposite sets): (7,7) 23,580 ($q=5$, 72), (9,7) 118,224 ($q=7$, 288),
(10,7) 225,128 ($q=8$, 217), (13,7) 1,064,448, (14,7) 1,774,584, (15,7) 2,484,720 ($q=11$, 756), (16,7) 4,025,508
($q=13$, 792); see research/d13D7/ and research/d10D7/checks/.

**The hub graph in practice.** (R3) only asks for a bipartite graph with same-side distances $\le6$ and degree
$\le q-j$ on the hubs of opposite owners. For $j=1,2,3$ at $q=11$ random graphs suffice. For $q=9$, $j=2$ ($d=7$,
up to $2|R|$ hubs per side) random graphs fail, but Haar graphs of non-abelian groups of order $\le 2|R|$ with
seven generators and diameter 7 are found in seconds by research/frontier/haar_gen3.c (PSL(2,11)×Z13 at 8,580;
a metacyclic group of order 8,612 = 2·4,306 failed).

### 7.3 Mixed sets (Lemma 3 beyond pairwise opposite sets)
- `ldual/ldual.c` (random greedy for Lemma 3 pairs; `ldual HEXBIN seed restarts [pure]`), best of 3 restarts:
  $q=3$: 20 (pure 16), $q=4$: 29 (pure 21), $q=5$: 39 (pure 30).
- Squad hexfam_r2 c7 (local search on pairs): $q=4$: 35, $q=5$: 48 (the structured pure set at $q=5$ has 72).
- **End-to-end check at $q=4$** (H(4) has no duality): the 35-set of c7 (research/squads/hexfam_r2/c7/runs/
  q4mix_s1_best_35.txt) satisfies Lemma 3 with 56 midpoints (`ldual/mixbuild.py`, an independent checker); $\sigma$
  built as in the proof of Lemma 3 satisfies (R2) at all 35 points; the 3-level graph with all 35 points freed and
  hubs for 3 of them ($K_{3,3}$ hub graph) has $n=8{,}196$, degrees 5–6 and **diameter 7** (apsp, all pairs).
  So Theorem 1 really does work for freed points at distance 4 from each other when $\sigma$ is a local duality
  but not a duality.
- For comparison, pure partial ovoids by ARW (`prod/mis.c` on the orthogonality graph, 90 s): $q=4$: 31,
  $q=5$: 61 (structured: 72).

### 7.4 Non-collinear sets by local search (calibration for $q=9$)
ARW (`prod/mis.c` on the collinearity graph, 60 s) reaches the Hoffman bound $q^4+q^2+1$ for $q=3$ (91) and $q=4$
(273), i.e. finds distance-2 ovoids, but only 484/651 at $q=5$ and 1,544/2,451 at $q=7$; at $q=9$ the best is
4,306/6,643 (65%). Whether $H(9)$ has a distance-2 ovoid is open as far as we know; one would give
$(11,7)\ \ge 411{,}866$ and $(12,7)\ \ge 690{,}872$ (with a hub graph of $2\cdot6643$ per side).

## 8. Lean (lean/BipartiteDD/HexagonD7/, no sorry, standard axioms only; Axioms.out.txt)

- `Hyp.ediam_le`, `exists_graph` (Defs, Cover, Diam, Main): **Theorem 1** for an arbitrary incidence structure
  with point–line walks of length $\le5$ and $\ge2$ lines per point and points per line, any $j$, any $\sigma$, $R$,
  hubs and hub graph satisfying (R1)–(R3) (with (R3) stated as: same-type hubs are within 6 through the hexagon or
  the hub graph), including the degree bound $q+1+j$ and the order $(2j+1)(|P|+|L|)+|V|+|U|$.
- `table_family` (Hexagon): for every finite field $F$, $q=|F|$, $j\le q$:
  $n_b(q+1+j,7)\ge2(2j+1)(q+1)(q^4+q^2+1)$ (the D = 7 table values), over the split Cayley hexagon of the
  existing library (`genPolygonGraph_hexagon_even`).
- `exists_local_duality` (Balls, LocalDual): **Lemma 2**, for any incidence structure with no digons and $q+1$
  lines per point and points per line.
- `freed_family` (Opposite, Family): for every finite field, $n_b(q+2,7)\ge6(q+1)(q^4+q^2+1)+2(q-1)$: greedy gives
  $q-1$ pairwise opposite points and lines because $(q-1)(q^2+q+1)^2<(q+1)(q^4+q^2+1)$, and the hub graph is
  $K_{q-1,q-1}$.

Not formalised: the duality case ($q=3^h$) and the specific large sets (their pairwise-opposite and hub-graph
conditions are finite checks done by C programs, far too large for the kernel).
