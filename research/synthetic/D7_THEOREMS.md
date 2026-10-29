---
title: "Diameter-7 cells from a spread and its whiskers: the freed sets and the bounds for every q"
author: "Degree–diameter lab, 29 October 2026 (job thm-conics)"
---

*Abstract.* The jobs "conics" and "conics-2" raised the lab's values at the diameter-7 cells $(14,7)$ to $(20,7)$ by
freeing, on the friendly transitions of the typed hexagon layouts, two sets: the points of the Hermitian spread $S$ of
$H(q)$, and the lines meeting a spread line $v$ together with an exact whisker set and the $q^2$ spread lines that carry
no whisker. Here these steps are turned into statements for every prime power $q$. (1) For any generalized hexagon of
order $(q,q)$, any spread $S$, any $v\in S$ and any whisker set $W$, the lines meeting $v$, the whiskers and the spread
lines missed by the whiskers form a dual segment set; for the exact whisker set of `POLISHED.md` (every odd $q$ and
every even $q\ge4$) it has exactly $q^4+q^2+q$ lines and is maximal, while the spread points form a segment set of
$(q+1)(q^3+1)$ points. (2) For $2k+1$ levels and any regular tournament and typing, the hub counts per side are at most
$\lfloor k/2\rfloor$ friendly sets plus non-friendly ones, with an exact second-order term; the alternating typing
attains this for every $k$. (3) With the $q^2+1$ points of an elliptic quadric section on the non-friendly
transitions, this gives, for every $k\ge2$ and every prime power $q\ge q_k$,
$$n_b(q+1+k,7)\ \ge\ 2(2k+1)(q+1)(q^4+q^2+1)+\begin{cases}k\,(q^4+2q^2+q+1)&k\text{ even},\\[2pt]
\tfrac{k-1}2\,(2q^4+q^3+q^2+2q+1)+(k+1)(q^2+1)&k\text{ odd},\end{cases}$$
with $q_2=16$, $q_3=q_4=23$, $q_5=29$, $q_k\le 300k$ in general. The hub graphs are given by a new explicit
construction (sums of blown-up hexagons); smaller $q$ are checked by computer where possible. The formulas reproduce
the vertex counts of all fifteen graphs built in the two jobs. At $(19,7)$ the formula equals the built value
$11{,}316{,}940$ and every ingredient is proved.

*Labels.* Every result is marked **Theorem** (proved here or in the cited note), **Computer-checked** (a program checked
it; the program is in the repository) or **Heuristic**, and **[new]** or **[restatement]**. "New" means new in the lab's
notes; the literature check of `D7_HEXAGON.md` §11 applies, and we did not search the literature again.

*Sources.* `research/synthetic/CONICS.md` §3.4 (branch `claude/conics-generalized-polygons-6gjqxi`);
`research/synthetic/conics2/README.md` (branch `claude/conics-2-diameter-7-ic0oat`, state of 11:44 UTC);
`research/theorems/D7_HEXAGON.md` (branch `claude/d7-hexagon-theorems-4w1prt`), whose Definitions 2.1, 3.1, Theorems
A, B, C, 3.4 and Proposition 5.2 are used throughout; `research/theorems/POLISHED.md` §6 (branch
`claude/thm-polish-2oddll`); `research/synthetic/SYNTHETIC.md` (branch `claude/synthetic-incidence-geometry-s4m08f`),
whose conventions we follow. Programs of this note: `research/synthetic/d7thm/`; squad round
`research/squads/d7thm-r1/`.

# 0. Setting

**Hexagons.** A generalized hexagon $\Gamma$ of order $(q,q)$ has $N=N(q)=(q+1)(q^4+q^2+1)$ points and as many lines;
$q+1$ points on a line and $q+1$ lines on a point. Distances are taken in the incidence graph $I$ (diameter $6$,
girth $12$); elements at distance $6$ are *opposite*. For an element $x$, $|\Gamma_i(x)|=(q+1)q^{i-1}$ for $1\le i\le5$.
A *spread* is a set of $q^3+1$ pairwise opposite lines; every line not in a spread $S$ meets exactly one line of $S$, in
one point (`D7_HEXAGON.md`, Lemma 1.2(c)). The example throughout is the split Cayley hexagon $H(q)$ in $Q(6,q)$ and
its Hermitian spread: the lines of $H(q)$ inside a hyperplane $\Pi$ with $\Pi\cap Q(6,q)$ elliptic (every $q$; [Th80]).

**Segment sets** (`D7_HEXAGON.md`, Definition 1.3). A point set $F$ is a *segment set* if for every $p\in F$ the points
of $F\setminus\{p\}$ collinear with $p$ lie on one line through $p$. A line set $G$ is a *dual segment set* if for every
$\ell\in G$ the lines of $G\setminus\{\ell\}$ that meet $\ell$ pass through one point of $\ell$. Both kinds have at most
$(q+1)(q^3+1)$ elements (`D7_HEXAGON.md`, Proposition 1.4).

**Layouts.** $L=2k+1$ *levels*, each a copy of $I$ of *type* $H$ (colour $\mathcal A$ = points, $\mathcal B$ = lines) or
$D$ (colour $\mathcal A$ = lines, $\mathcal B$ = points). The levels are the vertices of a *regular tournament* $T$: every
two levels are joined by exactly one *transition* $j\to j'$, and every level has $k$ outgoing and $k$ incoming
transitions. A transition is a bijection from the $\mathcal A$-elements of level $j$ to the $\mathcal B$-elements of
level $j'$; it is *friendly* if the types differ, and then it is the identity. `D7_HEXAGON.md` uses the rotational
tournament $j\to j+i$ ($1\le i\le k$, indices mod $L$); Theorem A and Theorem 3.4 there hold verbatim for every regular
tournament, since their proofs only use that every pair of levels is the pair of one transition. The *freed set* $R_t$
of a transition is the set of $\mathcal A$-elements whose matching edge is deleted. Level $j$ then has
$\alpha_j=\sum_{t\text{ out of }j}|R_t|$ free $\mathcal A$-slots and $\beta_j=\sum_{t\text{ into }j}|R_t|$ free
$\mathcal B$-slots. $K_{\mathcal B}\le\min_j\alpha_j$ hubs of colour $\mathcal B$ each take one free $\mathcal A$-slot in
every level, $K_{\mathcal A}\le\min_j\beta_j$ hubs of colour $\mathcal A$ one free $\mathcal B$-slot in every level, and a
bipartite *hub graph* $Y$ joins the two kinds of hubs.

**What repairs a transition.** Theorem B of `D7_HEXAGON.md`: a friendly transition is repaired if its freed set is a
segment set (source of type $H$) or a dual segment set (source of type $D$). Theorem C there, with Corollary 5.3(a): a
non-friendly transition $H\to H$ with matching $\sigma$ is repaired by a set $R$ of $m$ pairwise opposite points when
$\sigma$ maps $R$ onto $m$ pairwise opposite lines and the points collinear with $x$ onto the lines concurrent with
$\sigma(x)$ for every $x\in R$; such a $\sigma$ exists for every partial ovoid $R$ and every partial spread of the same
size. A $D\to D$ transition uses $\sigma^{-1}$ and frees $\sigma(R)$.

**Hub graphs.** $\mathrm{HG}(K_1,K_2;\delta)$ denotes a bipartite graph with colour classes of sizes $K_1$ and $K_2$,
maximum degree at most $\delta$, in which any two vertices *of the same colour* are at distance at most $6$.

**Theorem 0.1** (`D7_HEXAGON.md`, Theorem 3.4) [restatement]. If every transition is repaired, $K_{\mathcal B}\le\min
\alpha_j$, $K_{\mathcal A}\le\min\beta_j$ and the hub graph is an $\mathrm{HG}(K_{\mathcal B},K_{\mathcal A};q-k)$, then
the graph has maximum degree $q+1+k$ and diameter at most $7$, and
$$n_b(q+1+k,7)\ \ge\ 2(2k+1)N(q)+K_{\mathcal A}+K_{\mathcal B}.$$

The value $2(2k+1)N(q)$ alone (no freed sets, no hubs) is the value of the 2013 table at these cells [MS13].

**Notation for sizes.** $P(q)=(q+1)(q^3+1)=q^4+q^3+q+1$, $\Lambda(q)=q^4+q^2+q$, and $m$ the size of the non-friendly
sets. Note $P-\Lambda=q^3-q^2+1$.

# 1. The freed sets

## 1.1 The configuration

**Definition 1.1.** Let $S$ be a spread of $\Gamma$, $\mathcal P_S$ the set of points on its lines, and $v\in S$.
$\mathcal L_v$ is the set of the $q(q+1)$ lines other than $v$ that meet $v$. A point is *free* if it is at distance $5$
from $v$ and not in $\mathcal P_S$. A *whisker set* is a set $W$ of lines, each opposite $v$ and not in $S$, such that no
free point lies on two lines of $W$; it is *exact* if every free point lies on exactly one line of $W$. Finally
$$S_0(W)=\{n\in S\setminus\{v\}:\ n\text{ meets no line of }W\},\qquad R_L(W)=\mathcal L_v\cup W\cup S_0(W).$$

(This is the configuration of Theorem D, `POLISHED.md` §6.2 and `SYNTHETIC.md` §3.2, written without coordinates.)

**Lemma 1.2** [restatement, with the counts; Theorem]. (a) The points at distance at most $3$ from $v$ are the $q+1$
points of $v$ and the $q^2(q+1)$ points at distance $3$, each of which lies on exactly one line of $\mathcal L_v$.
(b) The points of $\mathcal P_S$ not on $v$ are at distance $5$ from $v$. (c) There are $q^3(q^2-1)$ free points. (d) A
line opposite $v$ and not in $S$ has exactly one point in $\mathcal P_S$ and $q$ free points. (e) A whisker set has at
most $q^2(q^2-1)$ lines, with equality if and only if it is exact.

*Proof.* (a) A point at distance $3$ from $v$ lies on a line meeting $v$; two such lines through it would close a circuit
of length at most $8$. Counting: $|\Gamma_3(v)|=(q+1)q^2$. (b) A point $x$ on a spread line $n\ne v$ has $d(x,v)$ odd and
$\ge d(n,v)-1=5$. (c) $|\Gamma_5(v)|=(q+1)q^4$, of which $q^3(q+1)$ lie in $\mathcal P_S$ by (b). (d) Every point of a
line opposite $v$ is at distance $5$ from $v$; the line meets exactly one line of $S$, in one point. (e) By (d) and
(c), counting incidences between free points and $W$. $\square$

## 1.2 Spread points and whiskers

**Proposition 1.3** (`D7_HEXAGON.md`, Proposition 1.4) [restatement; Theorem]. $\mathcal P_S$ is a segment set of
$P(q)=(q+1)(q^3+1)$ points, and no segment set is larger; equality holds only for the point sets of spreads.

**Theorem 1.4** [new in this form; Theorem]. Let $S$ be a spread, $v\in S$ and $W$ any whisker set.

(a) $R_L(W)=\mathcal L_v\cup W\cup S_0(W)$ is a dual segment set, and two of its lines that meet, meet in a point of
$\mathcal P_S$.

(b) $|R_L(W)|=q(q+1)+|W|+|S_0(W)|$.

(c) If $W$ is exact and every point of $\mathcal P_S$ not on $v$ lies on a line of $W$ or of $S_0(W)$, then every point
of $\Gamma$ lies on a line of $R_L(W)$, and no line can be added to $R_L(W)$: it is a maximal dual segment set.

(d) A line $n\in S\setminus\{v\}$ all of whose whiskers pass through one point of $n$ can be added to $R_L(W)$ as well.

*Proof.* (a) A line of $\mathcal L_v$ has one point on $v\subseteq\mathcal P_S$ and its other $q$ points at distance $3$
from $v$, so not in $\mathcal P_S$ (Lemma 1.2(b)). A whisker has one point in $\mathcal P_S$ and $q$ free points
(Lemma 1.2(d)). So every line of $\mathcal L_v\cup W$ has exactly one point in $\mathcal P_S$. Its other points are
either at distance $3$ from $v$, and then on no other line of $\mathcal L_v$ (Lemma 1.2(a)) and on no whisker (whose
points are at distance $5$), or free, and then on no line of $\mathcal L_v$ and on at most one whisker. So two lines of
$\mathcal L_v\cup W$ never meet outside $\mathcal P_S$. A line $n\in S_0(W)$ meets no line of $\mathcal L_v$ (whose
points are at distance at most $3$ from $v$, while those of $n$ are at distance $5$), no whisker (definition) and no
other spread line. So the lines of $S_0(W)$ are isolated, and for every other line $\ell$ of $R_L(W)$ the lines of
$R_L(W)$ meeting $\ell$ all pass through the unique point of $\ell$ in $\mathcal P_S$. (b) The three sets are disjoint:
whiskers are opposite $v$, lines of $\mathcal L_v$ are not, and neither kind is in $S$. (c) Points of $v$ and points at
distance $3$ from $v$ lie on lines of $\mathcal L_v$, free points on whiskers ($W$ exact), and the points of
$\mathcal P_S$ off $v$ by hypothesis. A line $\ell\notin R_L(W)$ then meets a line of $R_L(W)$ at each of its $q+1$
points, and these lines are different from each other (two points of $\ell$ on one line $\ne\ell$ is impossible), so
$R_L(W)\cup\{\ell\}$ is not a dual segment set. (d) Such an $n$ meets lines of $R_L(W)$ only in that one point, and
the whiskers through it already meet each other there. $\square$

For $W$ exact and $S_0(W)$ left out this is `CONICS.md`, Lemma 3.1; for the whisker set of `POLISHED.md` and its $q^2$
empty spread lines it is Proposition 1(c),(d) of `conics2/README.md`. The proof above uses only incidences.

**Proposition 1.5** [new; Theorem] (*where the room is*). Let $G$ be a dual segment set in which any two lines that meet
do so in a point of $\mathcal P_S$ (as in Theorem 1.4(a)). Then $|G\setminus S|\le q^4+q$, with equality if and only if
the lines of $G\setminus S$ cover every point outside $\mathcal P_S$ exactly once. Hence $|G|\le q^4+q+|G\cap S|$. For
an exact whisker set, $\mathcal L_v\cup W$ has exactly $q^4+q$ lines.

*Proof.* A line not in $S$ meets exactly one spread line, in one point, so it has exactly one point in $\mathcal P_S$
(a second point would lie on a second spread line). Its other $q$ points lie outside $\mathcal P_S$, and by hypothesis
these $q$-sets are disjoint for different lines of $G\setminus S$. There are $N-P(q)=q^5+q^2=q(q^4+q)$ points outside
$\mathcal P_S$. Finally $q(q+1)+q^2(q^2-1)=q^4+q$. $\square$

So within this class $R_L(W)$ can only grow by containing more spread lines, at most $q^3-q^2+1$ more; the general bound
$(q+1)(q^3+1)=q^4+q+(q^3+1)$ is the case where all spread lines are in $G$, which forces an ovoid.

**Lemma 1.6** [new; Theorem]. Let $W$ be exact. Every whisker meets exactly one line of $S\setminus\{v\}$, and a line
$n\in S\setminus\{v\}$ meets at most $q^2-1$ whiskers. So at least $q^2$ spread lines other than $v$ meet a whisker and
$|S_0(W)|\le q^3-q^2$. If every line of $S\setminus\{v\}$ meets either no whisker or $q+1$ whiskers, then
$|S_0(W)|=q^2$.

*Proof.* A whisker meets one line of $S$ (§0), not $v$, since it is opposite $v$. At a point $x$ of $n$ the $q+1$ lines are
$n$, the line through $x$ on the geodesic to $v$ (at distance $4$ from $v$, so not a whisker) and $q-1$ others. Hence
$n$ meets at most $(q+1)(q-1)$ whiskers, and $q^2(q^2-1)/(q^2-1)=q^2$. In the last case the lines meeting whiskers
number $q^2(q^2-1)/(q+1)=q^2(q-1)$, and $q^3-q^2(q-1)=q^2$. $\square$

## 1.3 The exact whisker set of `POLISHED.md`

In $H(q)$ with the coordinates of `POLISHED.md` §6.1 ($q$ odd) and §6.5 ($q$ even): $\Pi$ the elliptic hyperplane
$X_0+cX_4=0$ ($q$ odd, $-c$ a non-square) or $X_3=X_0+\delta X_4$ ($q$ even, $\mathrm{Tr}\,\delta=1$), $S$ its
Hermitian spread, $v=\langle e_1,e_6\rangle$, the hyperplanes $\Pi_z\supset v$ ($z=(\alpha,\beta)\in\mathbb F^2$) and
their spreads $S_z$, the function $\nu$ on the points of $\Pi$ off $v$, the zero-free cubic $G$ and $F(z)=G(z)/N(z)$
with $N$ the anisotropic norm form; $W=\{\ell\in S_z\setminus\{v\}: z\neq0,\ \nu(\ell\cap\Pi)=F(z)\}$ is exact for every
odd $q$ (Theorem 6.5) and every even $q\ge4$ (Theorem 6.14).

**Theorem 1.7** (`conics2/README.md`, Proposition 1(a),(b)) [restatement with proof; Theorem]. Let $q$ be odd, or even
with $q\ge4$, and $W$ the exact whisker set above. Then every point $X$ of $\mathcal P_S$ not on $v$ lies on exactly one
whisker if $\nu(X)\neq0$ and on none if $\nu(X)=0$; $\nu$ is constant on every line of $S\setminus\{v\}$. Hence every
line of $S\setminus\{v\}$ meets either $q+1$ whiskers, one at each of its points, or none, and
$S_0(W)=\{n\in S\setminus\{v\}:\nu(n)=0\}$ has exactly $q^2$ lines.

*Proof.* Whiskers through $X$ are whiskers whose point in $\Pi$ is $X$ (their other points are off $\Pi$). On $\Pi$ the
equation of $\Pi_z$ reduces to $\alpha X_2+\beta X_5=0$ (both parities), and $(X_2,X_5)\neq(0,0)$ because $X$ is not on
$v$ (`POLISHED.md`, Lemma 6.1(d) / 6.10). So the $z\neq0$ with $X\in\Pi_z$ form the punctured line
$\{tz_0:t\neq0\}$, $z_0=(X_5,-X_2)$. For each of them exactly one line of $S_z$ passes through $X$ (Lemma 6.1(b)); it is
not $v$, it is not in $S$ (6.1(e)), so it meets $\Pi$ only in $X$ (6.1(c)), and different $z$ give different lines
(6.1(e)). It is a whisker if and only if $\nu(X)=F(tz_0)$. As $G$ is a cubic form and $N$ a quadratic form,
$F(tz_0)=tF(z_0)$, and $F(z_0)\neq0$ since $G$ has no zero. So $t\mapsto F(tz_0)$ is a bijection of
$\mathbb F^\times$: one whisker through $X$ if $\nu(X)\neq0$, none if $\nu(X)=0$. $\nu$ is constant on spread lines by
`POLISHED.md`, Lemma 6.6(d) / 6.12(d). The count is Lemma 1.6. $\square$

**Corollary 1.8** [Theorem]. For every prime power $q$ with $q$ odd or $q\ge4$, in $H(q)$:
$R_H=\mathcal P_S$ is a segment set with $P(q)=q^4+q^3+q+1$ points, and $R_L=\mathcal L_v\cup W\cup S_0(W)$ is a maximal
dual segment set with $\Lambda(q)=q^4+q^2+q$ lines (Theorem 1.4 with Theorem 1.7). In the notation of Proposition 1.5,
$\mathcal L_v\cup W$ is extremal and $|R_L\cap S|=q^2$.

*Computer-checked.* `conics2/typed_build.py` asserts every statement of Theorem 1.7 and Corollary 1.8 for
$q=4,5,7,11,13,16$ inside the builds. Independently, squad round `d7thm-r1` (own code, not the builder): card c1 for
$q=3,5,7$ (hexagon built from the quadric and Tits' equations), card c2 for $q=9,11$, card c3 for $q=2,4,8$: exactness of
$W$, $\nu$ constant on spread lines, $0$ or $q+1$ whiskers per spread line, $|S_0|=q^2$ equal to the lines with $\nu=0$,
the dual segment property, $|R_L|=q^4+q^2+q$ ($6{,}651$ at $q=9$, $14{,}773$ at $q=11$, $276$ at $q=4$, $4{,}168$ at
$q=8$), maximality (every outside line tested), and the segment property of $\mathcal P_S$; card c2 also for every
admissible $c$ at $q=9,11$, card c3 for every admissible $(c_0,c_1)$ at $q=4,8$; negative controls fail as they should
(`research/squads/d7thm-r1/scoreboard.jsonl`).

*Remarks.* (i) $q=2$: Lemma 6.11 of `POLISHED.md` gives no zero-free $G$ (card c3 re-checked all four pairs), but an
exact whisker set of $12$ lines exists (`POLISHED.md`, Corollary 6.15), so Theorem 1.4 gives $|R_L|\ge18$; the largest
dual segment set of $H(2)$ has $25$ lines (`conics2/README.md` §3, SAT). (ii) $R_L$ is not maximum in general: $H(4)$ has
a dual segment set of $288>276$ lines (same place; it is not of the kind in Proposition 1.5). Whether
$q^4+q^2+q$ can be beaten for $q\ge5$ is open; by Proposition 1.5 a set of this kind would need more than $q^2$ spread
lines. (iii) For $q=3^h$ the pencils of an ovoid give a dual segment set of $P(q)$ lines, and the duality layout of
`D7_HEXAGON.md`, Corollary 8.2 is better than any typed layout. (iv) We know no coordinate-free description of the $q^2$
lines with $\nu=0$.

## 1.4 The non-friendly sets

**Proposition 1.9** (`D7_HEXAGON.md`, Lemma 1.2(a), Corollaries 5.3(a) and 9.1) [restatement; Theorem]. For every prime
power $q$, the $q^2+1$ points of an elliptic quadric section $Q^-(3,q)$ of $Q(6,q)$ are pairwise opposite in $H(q)$, and
with any $q^2+1$ lines of the Hermitian spread they give a local duality $\sigma$ as in Theorem C. So $m=q^2+1$ is
available on every non-friendly transition.

The lab's builds use larger non-friendly sets found by computer at $q=11$ ($m=768$, mirrored set) and $q=13$
($m=792$), and $m=q^2+1=257$ at $q=16$ (**Computer-checked**: the builder re-checks non-collinearity,
non-concurrency and the local duality at every point).

# 2. Slot counts

Let $T$ be a regular tournament on $2k+1$ levels with a typing. For a level $j$ let $f_j$ be the number of friendly
transitions out of $j$ and $g_j$ the number into $j$. With friendly sets of sizes $P$ (points, source $H$) and $\Lambda$
(lines, source $D$) and non-friendly sets of size $m$,
$$\alpha_j=f_jX_j+(k-f_j)m,\quad X_j=\begin{cases}P&\tau_j=H\\ \Lambda&\tau_j=D\end{cases},\qquad
\beta_j=g_jY_j+(k-g_j)m,\quad Y_j=\begin{cases}\Lambda&\tau_j=H\\ P&\tau_j=D\end{cases}$$
(a friendly transition into an $H$ level comes from a $D$ level, which frees lines). Put $a=\lfloor k/2\rfloor$ and
assume
$$P\ \ge\ \Lambda\ \ge\ m,\qquad \Lambda-m\ \ge\ a\,(P-\Lambda).\tag{$\ast$}$$
For the sets of §1, $(\ast)$ holds whenever $k\le 2q+1$ and $m\le q^2+1$, since then
$a(q^3-q^2+1)\le q^4-q^3+q\le q^4+q-1$; at $q=11$, $m=768$ it holds for $k\le23$, at $q=13$, $m=792$ for $k\le27$. The
bound needs $k\le q-1$ anyway (hub degree $q-k\ge1$).

**Theorem 2.1** [new; Theorem]. For every regular tournament on $2k+1$ levels and every typing, with $a=\lfloor
k/2\rfloor$:

(a) $\min_jf_j\le a$ and $\min_jg_j\le a$;

(b) if $k$ is even, it is impossible that $f_j\ge a$ at every level and $f_j\ge a+1$ at every $D$ level; likewise with
$g$ and $H$ levels;

(c) if $k$ is odd, it is impossible that $f_j\ge a$ and $g_j\ge a$ at every level, $f_j\ge a+1$ at every $D$ level and
$g_j\ge a+1$ at every $H$ level.

Consequently, under $(\ast)$: for $k$ even, $\min\alpha\le a(\Lambda+m)$ and $\min\beta\le a(\Lambda+m)$; for $k$ odd,
$\min\alpha,\min\beta\le aP+(a+1)m$ and $\min\alpha+\min\beta\le a(P+\Lambda)+2(a+1)m$.

*Proof.* Let $h$ and $d$ be the numbers of $H$ and $D$ levels. The $k-f_j$ non-friendly transitions out of an $H$ level
go to $H$ levels, so $\sum_{\tau_j=H}(k-f_j)=\binom h2$, and likewise $\sum_{\tau_j=D}(k-f_j)=\binom d2$ and the same with
$g$.

(a) If $f_j\ge a+1$ everywhere, then $\binom h2\le h(k-a-1)$ and $\binom d2\le d(k-a-1)$, so
$h+d\le 4k-4a-2\le 2k$, less than $2k+1$. For $g$ the same.

(b) $k=2a$. From $f_j\ge a$ on $H$ levels, $\binom h2\le ha$, so $h\le 2a+1$; from $f_j\ge a+1$ on $D$ levels,
$\binom d2\le d(a-1)$, so $d\le 2a-1$. Then $h+d\le4a<4a+1$. For $g$ exchange the roles of $H$ and $D$.

(c) $k=2a+1$. On $H$ levels $g_j\ge a+1$ gives $\binom h2\le ha$ (count non-friendly incoming transitions), so
$h\le2a+1$; on $D$ levels $f_j\ge a+1$ gives $\binom d2\le da$, so $d\le 2a+1$. Then $h+d\le4a+2<4a+3$.

Consequences. A level with $f_j\le a-1$ has $\alpha_j\le(a-1)P+(a+1)m\le a\Lambda+am$, by $(\ast)$. If $k$ is even and
$\min\alpha>a(\Lambda+m)$, every level has $f_j\ge a$, and every $D$ level $f_j\ge a+1$ (a $D$ level with $f_j=a$ has
$\alpha_j=a\Lambda+am$), contradicting (b). If $k$ is odd, a level with $f_j\le a$ has $\alpha_j\le aP+(a+1)m$, so by
(a) $\min\alpha\le aP+(a+1)m$, and the same for $\beta$. If $\min\alpha+\min\beta>a(P+\Lambda)+2(a+1)m$, both minima
exceed $a\Lambda+(a+1)m$; as before every level has $f_j,g_j\ge a$, $D$ levels $f_j\ge a+1$ and $H$ levels
$g_j\ge a+1$, contradicting (c). $\square$

**Theorem 2.2** [new; Theorem] (*the alternating layout*). Take the rotational tournament $j\to j+i$ ($1\le i\le k$) on
$\mathbb Z_{2k+1}$ and the typing $\tau_j=H$ for $j$ even, $\tau_j=D$ for $j$ odd ($0\le j\le 2k$; the levels $2k$ and $0$
are both of type $H$). Then $f_j=\lceil k/2\rceil$ for $0\le j\le k$, and for $j=k+t$ ($1\le t\le k$)
$$f_j=\begin{cases}k/2\ (t\text{ even, }H)\quad k/2+1\ (t\text{ odd, }D)&k\text{ even},\\
(k-1)/2\ (t\text{ odd, }H)\quad (k+1)/2\ (t\text{ even, }D)&k\text{ odd};\end{cases}$$
and $g_j=f_{2k-j}$. Hence, under $(\ast)$,
$$k\text{ even: }\ \min\alpha=\min\beta=\tfrac k2(\Lambda+m);\qquad k\text{ odd: }\ \min\alpha=\tfrac{k-1}2P+\tfrac{k+1}2m,
\quad\min\beta=\tfrac{k-1}2\Lambda+\tfrac{k+1}2m,$$
which are the bounds of Theorem 2.1.

*Proof.* For $j\le k$ the targets $j+1,\dots,j+k$ need no reduction mod $2k+1$, and exactly $\lceil k/2\rceil$ of them
have the parity opposite to $j$. For $j=k+t$ the targets are $j+1,\dots,2k$ ($k-t$ of them, $\lceil (k-t)/2\rceil$ of the
other parity) and $0,\dots,t-1$, of which $\lfloor t/2\rfloor$ (if $j$ is even) or $\lceil t/2\rceil$ (if $j$ is odd)
have the other parity; the four cases give the values stated. The reflection $j\mapsto 2k-j$ preserves types and
reverses every transition, so $g_j=f_{2k-j}$. For $k$ even the minimum $a$ of $f$ is attained at $D$ levels (odd
$j\le k$), so $\min\alpha=a\Lambda+am$; the minimum of $g$ is attained at $H$ levels, where friendly incoming sets are
lines: $\min\beta=a\Lambda+am$. For $k$ odd, $f_j=a$ only at $H$ levels and every $D$ level has $f_j=a+1$, whose
$\alpha_j=(a+1)\Lambda+am\ge aP+(a+1)m$ by $(\ast)$; so $\min\alpha=aP+(a+1)m$; $g_j=a$ only at $H$ levels, where
$\beta_j=a\Lambda+(a+1)m$. $\square$

So for the hubs the alternating layout is optimal among all regular tournaments and typings, and the slot counts are
$$K_{\mathcal B}(q,k)=K_{\mathcal A}(q,k)=\tfrac k2(\Lambda+m)\ (k\text{ even}),\qquad
K_{\mathcal B}=\tfrac{k-1}2P+\tfrac{k+1}2m,\ \ K_{\mathcal A}=\tfrac{k-1}2\Lambda+\tfrac{k+1}2m\ (k\text{ odd}).$$
For $k=1$ this is $m$ on both sides, `D7_HEXAGON.md` Corollary 9.1.

*The layouts of the builds* [Computer-checked against the builders' logs]. The free slots per level, in level order:

| $k$ | types | $\alpha_j$ | $\beta_j$ |
|---|---|---|---|
| 2 | $HDHDH$ (alternating) | $P{+}m,\ \Lambda{+}m,\ P{+}m,\ 2\Lambda,\ P{+}m$ | $\Lambda{+}m,\ 2P,\ \Lambda{+}m,\ P{+}m,\ \Lambda{+}m$ |
| 3 | $HHDHHDD$ | $P{+}2m,\ P{+}2m,\ 2\Lambda{+}m,\ 2P{+}m,\ 2P{+}m,\ 2\Lambda{+}m,\ 2\Lambda{+}m$ | $2\Lambda{+}m,\ 2\Lambda{+}m,\ 2P{+}m,\ \Lambda{+}2m,\ \Lambda{+}2m,\ 2P{+}m,\ 2P{+}m$ |
| 4 | $HHDHDHDHD$ (alternating, rotated) | $2P{+}2m,\ 2P{+}2m,\ 2\Lambda{+}2m,\ 2P{+}2m,\ 2\Lambda{+}2m,\ 2P{+}2m,\ 3\Lambda{+}m,\ 2P{+}2m,\ 3\Lambda{+}m$ | $2\Lambda{+}2m,\ 2\Lambda{+}2m,\ 3P{+}m,\ 2\Lambda{+}2m,\ 3P{+}m,\ 2\Lambda{+}2m,\ 2P{+}2m,\ 2\Lambda{+}2m,\ 2P{+}2m$ |

The $k=3$ layout of the builds is not the alternating one but has the same minima. With the values of each build these
vectors equal, entry by entry, the vectors printed by `typed_build.py` (`d7thm/cells.out`).

*Computer-checked.* `d7thm/slots.py`: for $k\le8$ every typing of the rotational tournament (the optimum is the one of
Theorem 2.2, numerically for $q=11$ with $m=768$, $q=13$ with $m=792$, $q=16,101,1009$); every labelled regular
tournament on $5$ and $7$ levels ($24$ and $2{,}640$) with every typing; SAT (CaDiCaL) on $9,11,13$ levels confirms
the impossibility statements. Independently squad card c6: all regular tournaments on $3,5,7$ levels, $200{,}000$
random ones on $9$ and $11$ levels, annealing, and the closed forms of Theorem 2.2 for $k\le40$. Card c6 also found that
without $(\ast)$ the value of $\min\alpha$ for odd $k$ changes (the $D$ levels become the minimum); this happens only for
$k$ far above $q$ (for instance $k\ge27$ at $q=11$), outside the range of the bound.

# 3. The bound

**Theorem 3.1** [new; Theorem]. Let $q$ be a prime power, $q$ odd or $q\ge4$, let $1\le k\le q-1$, and let
$K_{\mathcal B}(q,k)$, $K_{\mathcal A}(q,k)$ be the slot counts of Theorem 2.2 with $P=P(q)$, $\Lambda=\Lambda(q)$ and
$m=q^2+1$. If an $\mathrm{HG}(K_1,K_2;q-k)$ exists with $K_1\le K_{\mathcal B}$ and $K_2\le K_{\mathcal A}$, then
$$n_b(q+1+k,\,7)\ \ge\ 2(2k+1)N(q)+K_1+K_2 .$$

*Proof.* Take $2k+1$ copies of the incidence graph of $H(q)$, the alternating layout of Theorem 2.2, the identity on
friendly transitions with freed sets $R_H=\mathcal P_S$ (source $H$) and $R_L$ (source $D$) of Corollary 1.8, and on
non-friendly transitions the local duality $\sigma$ ($H\to H$) or $\sigma^{-1}$ ($D\to D$) of Proposition 1.9 with the
$q^2+1$ freed elements. Every friendly transition is repaired by Theorem B, every other one by Theorem C. Attach $K_1$
hubs of colour $\mathcal B$ and $K_2$ of colour $\mathcal A$ to free slots in any way (one slot per level each; unused
slots stay free) and use the given graph as hub graph. Theorem 0.1 applies. $\square$

The same holds with $m$ replaced by the size of any non-friendly set satisfying Theorem C, provided $(\ast)$ holds; and
for any generalized hexagon of order $(q,q)$ with a spread, an exact whisker set with the property of Theorem 1.7, and a
partial ovoid, by the same proof.

**Corollary 3.2** [new; Theorem when the hub graph exists]. With full slots ($K_1=K_{\mathcal B}$, $K_2=K_{\mathcal A}$)
Theorem 3.1 gives $n_b(q+1+k,7)\ge F_k(q)$, where
$$F_k(q)=2(2k+1)(q+1)(q^4+q^2+1)+\begin{cases}k\,(q^4+2q^2+q+1),&k\text{ even},\\[2pt]
\tfrac{k-1}2\,(2q^4+q^3+q^2+2q+1)+(k+1)(q^2+1),&k\text{ odd}.\end{cases}$$
In particular
$$F_2(q)=10N(q)+2q^4+4q^2+2q+2,\quad F_3(q)=14N(q)+2q^4+q^3+5q^2+2q+5,\quad F_4(q)=18N(q)+4q^4+8q^2+4q+4.$$
The gain over the 2013 table value $2(2k+1)N(q)$ is $kq^4+O(q^2)$ for $k$ even and $(k-1)q^4+\frac{k-1}2q^3+O(q^2)$ for
$k$ odd; the earlier general statement, `D7_HEXAGON.md` Corollary 9.3 ($k=2$), gave $2(q+2)(q^2+1)\approx2q^3$, and
none was stated there for $k\ge3$. With a larger non-friendly set $m$ the formula changes by $k(m-q^2-1)$ for $k$ even and
$(k+1)(m-q^2-1)$ for $k$ odd.

*Computer-checked* (`d7thm/cells.py`). The closed forms agree with the slot formulas for $q\le37$, $k\le6$.

# 4. Hub graphs

The bound needs $\mathrm{HG}(K_{\mathcal B},K_{\mathcal A};q-k)$ with $K\approx\lfloor k/2\rfloor q^4$ hubs per side and
degree $q-k$. The Moore-type bound for same-colour distance $6$ is about $(q-k)^6$, so there is room, but the explicit
hub graph of `D7_HEXAGON.md` (Lemma 7.1, a plane with pendant trees) has only about $\frac4{27}(q-k)^4$ vertices per
colour. Write $K_0(s)=(s+1)(s^4+s^2+1)$ for the number of points of a hexagon of order $(s,s)$.

**Lemma 4.1** (*blown-up hexagon*) [Theorem; elementary]. Let $s$ be a prime power and $c\ge1$. Replace every point and
every line of $H(s)$ by between $1$ and $c$ copies, and join two copies when the originals are incident. The result is
an $\mathrm{HG}(K_1,K_2;c(s+1))$ for any chosen $K_1,K_2\in[K_0(s),cK_0(s)]$, and any two of its vertices of different
colours are at distance at most $5$.

*Proof.* A path between copies of $x\neq y$ projects to a walk from $x$ to $y$ of the same length, and a geodesic from $x$
to $y$ lifts to copies, so the distance is $d(x,y)$; two copies of one element are at distance $2$. A copy of $x$ has
degree $\sum_{y\ \mathrm I\ x}t_y\le c(s+1)$. $\square$

**Lemma 4.2** (*sums*) [new; Theorem]. Let $Y_1,\dots,Y_r$ be bipartite graphs with colour classes $(A_i,B_i)$, each with
all same-colour distances at most $6$, and for $i<r$ also all different-colour distances at most $5$. Suppose
$|A_j|\le|B_i|$ and $|B_j|\le|A_i|$ for $i<j$. For every $i<j$ add an injective map $A_j\to B_i$ and an injective map
$B_j\to A_i$, as edges. The result is an $\mathrm{HG}(\sum|A_i|,\sum|B_i|;\ \max_i\Delta(Y_i)+r-1)$.

*Proof.* The new edges join the colours $A$ and $B$, so the graph is bipartite with classes $\bigcup A_i$, $\bigcup B_i$.
A vertex of $Y_i$ gains one edge to each $Y_j$, $j<i$, and at most one from each $Y_j$, $j>i$. Same-colour pairs inside
one $Y_i$ are at distance at most $6$ in $Y_i$. For $x\in A_j$ and $z\in A_i$ with $i<j$, $x$ has a neighbour
$b\in B_i$, and $d_{Y_i}(b,z)\le5$ since $i<r$; so $d(x,z)\le6$. The same for $B$. $\square$

**Lemma 4.3** (`D7_HEXAGON.md`, Lemma 7.1, with the colours sized separately) [restatement; Theorem]. Let $s$ be a prime
power, $n=s^2+s+1$, $t=\delta-s-1\ge0$, $u=\delta-1$. Attach to the incidence graph of $\mathrm{PG}(2,s)$ $c_P$ pendant
vertices at the points and $c_L$ at the lines (at most $t$ per core vertex), and $g_P$, $g_L$ pendant vertices below
these (at most $u$ per vertex). This is an $\mathrm{HG}(n+c_L+g_P,\ n+c_P+g_L;\ \delta)$. *Proof.* The distance argument
of Lemma 7.1 does not use the numbers of pendant vertices. $\square$ (Different-colour distances can be $7$ here, so such
a part can only be the last part $Y_r$ in Lemma 4.2; squad card c5 confirmed this with a negative control.)

**Theorem 4.4** [new; Theorem]. Let $k\ge2$. An $\mathrm{HG}(K_{\mathcal B}(q,k),K_{\mathcal A}(q,k);q-k)$ (full slots of
Theorem 2.2, $m=q^2+1$) exists

(a) for every prime power $q\ge300k$;

(b) for $2\le k\le12$, for every prime power $q\ge q_k$, where

| $k$ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $q_k$ | 16 | 23 | 23 | 29 | 23 | 37 | 29 | 41 | 32 | 49 | 41 |

(For $k=10$ every prime power $q\ge 32$; the values are not monotone in $k$ because prime powers are irregular.)

*Proof.* (a) Write $K_{\mathcal A}\le K_{\mathcal B}$ (true for the slot counts) and $x=K_{\mathcal A}^{1/5}-1$. By
Nagura's theorem (for $y\ge25$ there is a prime in $(y,\frac65y)$; J. Nagura, Proc. Japan Acad. 28 (1952) 177–181) there
is a prime $s$ with $x/1.2<s<x$ (here $x\ge q^{4/5}-1>25$). Then $K_0(s)<K_0(x)<(x+1)^5=K_{\mathcal A}$, and
$K_{\mathcal B}/K_0(s)<1.2^5K_{\mathcal B}/x^5\le 2.4884\,(1+1/q)/(1-5q^{-4/5})<3$ (using $(1-u)^5\ge1-5u$,
$K_{\mathcal A}\ge q^4$ and $K_{\mathcal B}/K_{\mathcal A}\le P/\Lambda\le1+1/q$). So Lemma 4.1 with $c=3$ gives an
$\mathrm{HG}(K_{\mathcal B},K_{\mathcal A};3(s+1))$, and $3(s+1)<3K_{\mathcal A}^{1/5}\le 3k^{1/5}(q+1)^{4/5}$ (as
$K_{\mathcal B}\le k(q+1)^4$). For $q+1\ge300k$, $3k^{1/5}(q+1)^{4/5}=3(q+1)\,(k/(q+1))^{1/5}\le 3(q+1)/300^{1/5}<0.97(q+1)-k$...
more simply $3k^{1/5}(q+1)^{4/5}\le 3\cdot300^{-1/5}(q+1)=0.959\,(q+1)\le q-k$ when $q+1\ge300k$ and $k\ge2$. (b) For
$q\le200$ the program `d7thm/hubsum.py` writes for each $(q,k)$ an explicit decomposition into parts of Lemmas 4.1–4.3,
combined by Lemma 4.2; each line of `d7thm/hubsum.out` can be checked by hand (sizes add up, the order condition,
degrees). Examples: $q=16$, $k=2$, $K=66{,}065$: $H(8)+H(7)+H(5)+H(5)+$ a pendant-tree part with $1{,}196$ vertices
per colour of degree $10$; degrees $9+4,\ 8+4,\ 6+4,\ 6+4,\ 10+4\le14$. $q=23$, $k=3$: $H(11)+H(9)+H(8)$ blown up by
$2$ to $49{,}506$ and $37{,}867$. For $200<q\le2\cdot10^5$ Lemma 4.1 alone suffices (`d7thm/hubcap.py`, which finds $s$
and $c$ for every such $q$); for $q>2\cdot10^5\ge300k$ use (a). $\square$

**Computer-checked hub graphs below $q_k$** (`d7thm/hgcheck.c`, own code: bit-parallel breadth-first search from every
hub; `d7thm/hgcheck_lab.out`, `d7thm/hgrun.out`). The lab's stored hub graphs, read from the solution files, re-checked
standalone: $\mathrm{HG}(15541,15541;9)$ [(14,7)], $\mathrm{HG}(29535,29535;11)$ [(16,7)], $\mathrm{HG}(32356,30327;10)$
and $\mathrm{HG}(32356,30158;10)$ [(17,7)], $\mathrm{HG}(25308,25308;9)$ [(18,7), PSL(2,37)],
$\mathrm{HG}(66065,66065;14)$ [(19,7)], $\mathrm{HG}(70163,66322;13)$ [(20,7)]: all VALID. The two cluster-assisted ones
[(15,7) $16{,}152$, (18,7) $34{,}440$] are not hub graphs in this sense (their same-colour pairs are joined through the
levels; $452{,}256$ and $654{,}360$ ordered pairs are far in the hub graph alone, the second as reported in
`conics2/README.md`); their condition (HG) is covered by the all-pairs checks. New random graphs at the slot counts of
Theorem 2.2 with $m=q^2+1$: GAPRESULTS

**Heuristic.** A random bipartite graph of degree $\delta$ has same-colour distances at most $6$ once $K$ is well below
$\delta^6/\log$; the failures at $(q,k)=(11,3)$ ($\delta=8$, $K\approx16{,}000$) and $(13,4)$ ($\delta=9$,
$K\approx58{,}000$) are where this runs out, and there the lab used Haar graphs over $\mathrm{PSL}(2,p)$ and paths
through the levels.

# 5. The cells

TABLECELLS

# 6. Summary: what is new

NEWSUMMARY

# Appendix: files

FILES

# References

- [MS13] M. Miller, J. Širáň, Moore graphs and beyond: a survey of the degree/diameter problem, Electron. J. Combin.,
  Dynamic Survey DS14 (2013).
- [Na52] J. Nagura, On the interval containing at least one prime number, Proc. Japan Acad. 28 (1952) 177–181.
- [Th80] J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A 29 (1980) 87–93.
- [VM98] H. Van Maldeghem, Generalized Polygons, Birkhäuser, 1998.
