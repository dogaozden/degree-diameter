# Polished theorems: statements in coordinates, proofs, neighbourhoods, cells, status

Prepared for Ignacio López and Gabriela Araujo-Pardo. Draft of 2026-10-25 (job thm-polish, branch
`claude/thm-polish-2oddll`). Sources: `research/NOTE.md`, `research/geometry/geometry.tex` and `PROOFREAD.md`,
`research/plus2/coords/coords.tex`, `research/p4/regular/REPORT.md`, `research/theorems/REGULARITIES.md`,
`research/gq4*`, `lean/`. Nothing here is a new result: this file restates the lab's earlier theorems with complete
proofs, writes every construction in projective coordinates, and lists the neighbourhood of every new vertex so that
degrees and diameter can be checked by hand.

For each result we give: **Statement** (in coordinates), **New vertices** (exact neighbourhoods), **Proof**,
**Cells** (the 2013 table value against ours), **Status**. Status words:

- *paper proof*: a complete written proof (the one given here);
- *computer-checked*: the graphs were built from the definition and checked (bipartite, degrees, exact diameter by
  breadth-first search from every vertex), by at least two independent programs;
- *Lean-checked*: proved in Lean 4 with Mathlib (Lean 4.34.1). `#print axioms` lists only `propext`,
  `Classical.choice`, `Quot.sound`; there is no `sorry`, `admit`, new `axiom` or `native_decide` in the library.
  Section 9 says exactly which statements are covered.

## Changes from the earlier drafts

Errors and corrections found while preparing this version (none affects a theorem or a record value):

1. **The 2013 baseline at $D=3$.** The README and Table 1 of `geometry.tex` list $(13,3)=274$ and $(15,3)=374$ as
   "table" values. Those are the later values of Araujo-Pardo and López [AL20] (Graphs Combin. 2022). The 2013 survey
   table (Miller–Širáň, Electron. J. Combin. DS14v2, Table 4) has $270$ and $370$ there. Both columns are now shown.
   Every other cell used below has the same value in the survey and in the wiki values read on 2026-10-10
   (`research/frontier/TABLE.md`).
2. **Corollary C1 needs no Klein correspondence.** `NOTE.md` derived the $(16,4)$ graph through $Q(4,q)$ and listed
   the Klein step as not formalised. The same construction is the point–line dual one in $W(3,q)$ itself: one copy of
   each point of the Singer 2-ovoid and two copies of each line of a regular spread (Section 5). We checked this form
   by computer for $q=3,5$ (scratch script, orders 120 and 416, diameter 4).
3. **Lean status in `NOTE.md` §7 is out of date.** Theorem B *with* stand-ins is now in Lean (`GQST.standin_gqst`),
   and so are the regular versions; see Section 9.
4. **`NOTE.md` open problem 3** ($q^2+1$ shadow lines on $Q(4,q)$ with one ovoid of clones, $q$ odd) is settled
   negatively by `geometry.tex`, Proposition `prop:shadowbound` (at most $q^2-q+2$). `NOTE.md` is superseded on this point.
5. **Theorem A in nicer coordinates.** The pair $\kappa_1=1/2$, $\kappa_2=1/(2\varepsilon)$ satisfies
   $\kappa_1\kappa_2=1/(4\varepsilon)$, so the two quadrics can be written $2X_0X_1=X_2^2-\varepsilon X_3^2$ and
   $2\varepsilon X_0X_1=X_2^2-\varepsilon X_3^2$. Same theorem; checked by computer for $q=3,5,7,9$.
6. **The fourth hat needs $q\ge3$ without coordinates and $q\ge4$ in coordinates.** The coordinate-free statement
   uses four points of a line ($q+1\ge4$); the coordinate version labels them by four field elements $0,1,a,c$
   ($q\ge4$). Both are stated as such below; no table cell has $q=3$.
7. **Delorme's two 1985 papers.** Which of [D85a] and [D85b] contains the doubling with levels and the $D=4,6$ table
   constructions is not confirmed (we have not seen the full texts). Both are cited.
8. **Theorem R is explicit except for the completing anti-flags.** The completion step is an existence argument
   (Lemma 7.2). We now say this plainly: every neighbourhood is listed except the $(m-1)$ completing anti-flags at the
   deficient vertices, and neither the maximum degree nor the diameter depends on that choice.
9. **Printed matching in [AL20].** Already noted in `geometry.tex`: with the index set $\mathbb F\setminus\{0,1,a\}$
   four vertices keep degree $q+1$; with $\mathbb F^*$ the graph is $(q+2)$-regular as intended. Kept (Remark 2.7).

## Summary of cells

$M_b$ is the bipartite Moore bound. "2013" is the survey table (DS14v2, Table 4, as of March 2013); "wiki" is the
current CombinatoricsWiki value where it differs. All our graphs were rebuilt and checked by the coordinator.

| $(\Delta,D)$ | $M_b$ | 2013 | wiki | ours | regular? | result | status |
|---|---:|---:|---:|---:|---|---|---|
| (11,3) | 222 | 190 | 190 | **192** | yes | fourth hat, $q=9$ | paper, computer, Lean |
| (13,3) | 314 | 270 | 274 | **276** | yes | fourth hat, $q=11$ | paper, computer, Lean |
| (15,3) | 422 | 370 | 374 | **376** | yes | fourth hat, $q=13$ | paper, computer, Lean |
| (7,4) | 518 | 346 | | **359** | no (350 regular) | Theorem B on $Q(4,5)$, explicit example | computer, Lean (graph) |
| (11,4) | 2222 | 1734 | | **1782** | yes | Theorem A, $q=9$ | paper, computer, Lean |
| (13,4) | 3770 | 3064 | | **3146** | yes | Theorem A, $q=11$ | paper, computer, Lean |
| (15,4) | 5910 | 4946 | | **5070** | yes | Theorem A, $q=13$ | paper, computer, Lean |
| (16,4) | 7232 | 5134 | | **5440** | yes | Prop. C + Cor. C1, $q=13$ | paper, computer, Lean |
| (7,5) | 3110 | 1134 | | **1152** | yes | Haar lemma, $S_4\times\mathbb Z_{24}$ | paper, computer, Lean |
| (9,5) | 22222 | 2496 | | **2662** | yes | Haar lemma, Heisenberg group mod 11 | paper, computer, Lean |
| (7,6) | 18662 | 8992 | | **9592** | 9348 | Theorem D / R, $q=5$ | paper, computer, Lean |
| (11,6) | 222222 | 142464 | | **148944** | 147500 | Theorem D / R, $q=9$ | paper, computer, Lean (theorem) |
| (13,6) | 542906 | 374452 | | **388972** | 386328 | Theorem D / R, $q=11$ | paper, computer, Lean (theorem) |
| (15,6) | 1158390 | 842048 | | **870440** | 866068 | Theorem D / R, $q=13$ | paper, computer, Lean (theorem) |
| (16,6) | 1627232 | 884062 | | **940846** | 927724 | Theorem D / R, $q=13$, $m=3$ | paper, computer, Lean (theorem) |

"Lean (theorem)": the general theorem is Lean-checked for every $q$, so these orders are Lean-checked lower bounds
(Section 9); the graphs themselves are too large for a kernel certificate. "Lean (graph)": the specific graph is
kernel-checked. The 2013 values at $D=4$ and $D=6$ are Delorme's [D85a, D85b]: $2q^3+3q^2+3q+6$ at $D=4$ and
$2(q+1)(q^4+q^2+1)+q^4+4q^3+q^2+4q+10$ at $D=6$, $\Delta=q+2$ (Example 3.6 and Remark 6.5). At $(8,5)$ the Haar lemma
gave $1764>1710$ (Lean-checked), since superseded by a $2048$-vertex lift that is not covered here.

---

## 0. Conventions

An *incidence structure* $\mathcal S=(\mathcal P,\mathcal L,\mathrm I)$ has points, lines and a symmetric incidence
relation; repeated lines are allowed. Its *incidence graph* $\Gamma(\mathcal S)$ has vertex set
$\mathcal P\cup\mathcal L$ and the flags as edges; it is bipartite with the points on one side. Every bipartite graph
with a chosen 2-colouring is of this form, so

$$n_b(\Delta,D)=\max\{|\mathcal P|+|\mathcal L|:\ \text{every element has at most }\Delta\text{ neighbours},\ \operatorname{diam}\Gamma(\mathcal S)\le D\},$$

$$M_b(\Delta,D)=2\bigl(1+(\Delta-1)+\dots+(\Delta-1)^{D-1}\bigr).$$

Distances $d(x,y)$ are in $\Gamma(\mathcal S)$. *Collinear* points are distinct points on a common line; *concurrent*
lines are distinct lines on a common point. $\mathbb F=\mathrm{GF}(q)$. Points of $\mathrm{PG}(n,q)$ are written
$(x_0:\dots:x_n)$; lines of $\mathrm{PG}(2,q)$ are written $[u:v:w]$, with $(x:y:z)\,\mathrm I\,[u:v:w]$ iff
$ux+vy+wz=0$. $\chi$ is the quadratic character of $\mathbb F$ ($q$ odd), with $\chi(0)=0$.

**Lemma 0.1 (diameter in geometric terms).** Let $\mathcal S$ have no isolated element and $D\ge2$.
(i) If $D$ is even, $\operatorname{diam}\mathcal S\le D$ iff $d(p,L)\le D-1$ for every anti-flag $(p,L)$.
(ii) If $D$ is odd, $\operatorname{diam}\mathcal S\le D$ iff any two points, and any two lines, are at distance at most
$D-1$. In particular: diameter $\le3$ iff any two points are collinear and any two lines concurrent; diameter $\le4$
iff for every anti-flag $(p,L)$ some point of $L$ is collinear with $p$.

*Proof.* (i) Let $p\ne p'$ be points and $L$ a line on $p'$. If $p\,\mathrm I\,L$, $d(p,p')=2$; otherwise
$d(p,p')\le d(p,L)+1\le D$. Lines likewise. (ii) For an anti-flag $(p,L)$ take $p'\,\mathrm I\,L$; then
$d(p,L)\le d(p,p')+1\le D$. The converses hold by parity. $\square$

**Lemma 0.2 (adding flags, deleting twins).** (a) Adding flags to an incidence structure cannot increase any distance
and keeps the incidence graph bipartite. (b) If two lines have the same set of points, deleting one of them changes no
distance between the remaining elements (a shortest path through the deleted line can use its twin instead; it does
not already contain the twin, since then it could be shortened). $\square$

---

## 1. Doubling with levels, and the hat lemma

Delorme and Farhi [DF84] observed that a *duplicate* of a vertex (a new vertex with the same neighbours) does not
increase the diameter. Delorme [D85a, D85b] refined this into a doubling with levels and used it for the old
$D=4$ and $D=6$ table values. We state it for incidence structures.

### 1.1 The operation

Let $\mathcal A=(\mathcal A_0\supseteq\mathcal A_1\supseteq\dots\supseteq\mathcal A_r\supseteq\mathcal A_{r+1}=\emptyset)$
be a filtration of a set $\mathcal A_0$ of elements (points and lines may be mixed). The *level* of $x$ is
$\lambda(x)=\max\{k:x\in\mathcal A_k\}$, and $\lambda(x)=-1$ if $x\notin\mathcal A_0$. Fix $m\ge2$. Two words over
$[m]=\{1,\dots,m\}$ are *comparable* if one is a prefix of the other.

**Definition 1.1.** The $m$-fold doubling $\mathcal S^{(m)}_{\mathcal A}$ has the *versions* $x^w$, $x$ an element of
$\mathcal S$ and $w\in[m]^{\lambda(x)+1}$ (a point if $x$ is a point, a line if $x$ is a line), and

$$x^w\ \mathrm I\ y^u\iff x\ \mathrm I\ y\ \text{and}\ w,u\ \text{are comparable}.$$

So an element of level $-1$ has one version (identified with $x$), adjacent to *every* version of each of its
neighbours; and a version $x^w$ of level $k\ge0$ is adjacent, for each neighbour $y$ of $x$, to the single version
$y^{w_1\cdots w_{j+1}}$ if $\lambda(y)=j\le k$, and to the $m^{j-k}$ versions $y^{wu}$ ($|u|=j-k$) if $\lambda(y)=j>k$.
This is the exact neighbourhood of every version.

The map $x^w\mapsto x$ preserves incidence, so $d(x^w,y^u)\ge d(x,y)$ for all versions.

Conditions on $\mathcal A$ (with $D\ge2$):

- **(L0)** every element outside $\mathcal A_0$ is incident with at most one element of $\mathcal A_0$;
- **(L1)** for every $i\ge0$: every element incident with an element of $\mathcal A_{i+1}$ lies in $\mathcal A_i$, and
  every element of $\mathcal A_i\setminus\mathcal A_{i+1}$ is incident with at most one element of $\mathcal A_{i+1}$;
- **(C$_D$)** for any two elements $x,y$ (possibly $x=y$) in the same connected component of the substructure induced
  on $\mathcal A_0$, there is $z\notin\mathcal A_0$ with $d(x,z)+d(z,y)\le D$.

### 1.2 Delorme's theorem

**Theorem 1.2 (Delorme [D85a, D85b]).** Let $\mathcal S$ have diameter at most $D\ge2$ and let $m\ge2$.

- (a) If (C$_D$) holds, $\mathcal S^{(m)}_{\mathcal A}$ has diameter at most $D$.
- (b) If (L0) and (L1) hold, every version satisfies $\deg x^w\le\deg x+m-1$, with equality only if $x$ is incident
  with an element of level $\lambda(x)+1$.
- (c) $\mathcal S^{(m)}_{\mathcal A}$ has $|\mathcal P|+(m-1)\sum_{k\ge0}m^k|\mathcal A_k\cap\mathcal P|$ points and
  $|\mathcal L|+(m-1)\sum_{k\ge0}m^k|\mathcal A_k\cap\mathcal L|$ lines.
- (d) Conversely, if $\mathcal S^{(m)}_{\mathcal A}$ has diameter at most $D$, the conclusion of (C$_D$) holds for every
  pair $x,y\in\mathcal A_0$.

*Proof.* (c) An element of level $k$ has $m^{k+1}=1+(m-1)(1+m+\dots+m^k)$ versions.

(b) Let $\lambda(x)=k$. By the description after Definition 1.1, only neighbours of level $>k$ contribute more than
one version. If $k=-1$, (L0) gives at most one neighbour in $\mathcal A_0$, of level exactly 0 (a neighbour in
$\mathcal A_1$ would put $x$ in $\mathcal A_0$ by (L1)); it contributes $m$ versions. If $k\ge0$, (L1) with $i=k$ gives
at most one neighbour in $\mathcal A_{k+1}$, and (L1) with $i=k+1$ gives none in $\mathcal A_{k+2}$; that neighbour
contributes $m$ versions. So $\deg x^w\le\deg x-1+m$.

(a) For an infinite word $\omega$ the *sheet* $\Sigma_\omega$ is the set of versions $x^w$ with $w$ a prefix of $\omega$.
It contains one version of each element, and $x^w\mapsto x$ is an isomorphism from the substructure on $\Sigma_\omega$
onto $\mathcal S$. Two versions with comparable words lie in a common sheet, hence are at distance $\le D$. Let
$x^w,y^u$ have incomparable words; both are non-empty, so $x,y\in\mathcal A_0$. If $x,y$ are in different components
of the substructure on $\mathcal A_0$, a shortest path $x=z_0,\dots,z_k=y$ ($k\le D$) passes through some
$z_i\notin\mathcal A_0$, whose unique version lies in every sheet. Lift $z_0,\dots,z_i$ into a sheet through $x^w$ and
$z_i,\dots,z_k$ into a sheet through $y^u$: a path of length $k$. If $x,y$ are in the same component (including
$x=y$), (C$_D$) gives $z\notin\mathcal A_0$ with $d(x,z)+d(z,y)\le D$, and the same lifting gives a path of length
$\le D$.

(d) Take versions $x^w$, $y^u$ with $w$ starting with the letter 1 and $u$ with the letter 2, and a path of length
$\le D$ between them. Consecutive versions on it have comparable words, and comparable non-empty words start with the
same letter; so some version on the path has the empty word, i.e. is an element $z\notin\mathcal A_0$. Projecting the
path gives a walk $x\to z\to y$ of length $\le D$. $\square$

### 1.3 The hat lemma

A *generalized $n$-gon* is an incidence structure whose incidence graph has diameter $n$ and girth $2n$; it has
order $(s,t)$ if lines have $s+1$ points and points are on $t+1$ lines.

**Lemma 1.3 (hat lemma).** Let $\mathcal S$ be a generalized $n$-gon of order $(s,t)$, $s,t\ge1$, and
$\mathcal A_0$ a set of elements. Then (C$_n$) holds iff every connected component of the substructure induced on
$\mathcal A_0$ is a tree of diameter at most $n-2$.

*Proof.* Suppose a component $B$ contains a path $x=z_0,\dots,z_{n-1}=y$ of length $n-1$ (it does if $B$ has diameter
$\ge n-1$, and if $B$ contains a cycle, since cycles have length $\ge2n$). By the girth this is the only path of length
$\le n-1$ from $x$ to $y$, so $d(x,y)=n-1$. If $d(x,z)+d(z,y)\le n$ then, by parity, $d(x,z)+d(z,y)=n-1$, so $z$ lies
on a shortest $x$–$y$ path, i.e. $z=z_i\in\mathcal A_0$. So (C$_n$) fails.

Conversely let $B$ be a tree of diameter $\le n-2$, $x,y\in B$, and $P$ the path from $x$ to $y$ in $B$, of length
$d$. $\Gamma(\mathcal S)$ is connected and has cycles, so $B\neq\Gamma(\mathcal S)$ and some element of $B$ has a
neighbour outside $\mathcal A_0$. Let $k$ be the least distance in $B$ from $P$ to such an element $u$, and $z$ a
neighbour of $u$ outside $\mathcal A_0$. Then $d(x,z)+d(z,y)\le d+2k+2$. If $k=0$ this is $\le n$. If $k\ge1$, every
element of $B$ at distance $<k$ from $P$ has all its neighbours in $B$, and every element has at least two neighbours
($s,t\ge1$). So we can walk $k$ steps away from $P$ starting at $x$, and $k$ steps away from $P$ starting at $y$
(along two different neighbours if $x=y$); in the tree $B$ this gives a path of length $d+2k$. Hence $d+2k\le n-2$
and $d(x,z)+d(z,y)\le n$. $\square$

**Corollary 1.4.** In a generalized $n$-gon of order $(s,t)$, $s,t\ge1$, and for any filtration and $m\ge2$:
$\mathcal S^{(m)}_{\mathcal A}$ has diameter at most $n$ iff every component of the substructure on $\mathcal A_0$ is a
tree of diameter at most $n-2$. (Theorem 1.2(a),(d) and Lemma 1.3.) For $n=3$ the allowed components are single
elements and flags; for $n=4$ also *stars* (a point with some lines on it, or a line with some of its points); for
$n=6$ trees of diameter $\le4$.

**Proposition 1.5 (diameter 3 needs patches).** In a projective plane, if $\mathcal A$ satisfies (L0), (L1) and
(C$_3$), then $\mathcal A_0$ has at most one point and at most one line, and $\mathcal A_1=\emptyset$.

*Proof.* If $x\ne y$ are points of $\mathcal A_0$, the line $xy$ is either outside $\mathcal A_0$ and incident with two
elements of $\mathcal A_0$ (against (L0)), or in $\mathcal A_0$, and then $x,xy,y$ is a path of length $2>n-2$ in one
component (against Lemma 1.3). Lines likewise. An element of $\mathcal A_1$ would have its $q+1\ge3$ neighbours in
$\mathcal A_0$ by (L1). $\square$

So pure doubling gains at most 2 elements in a projective plane; the hats of Section 2 double flags and then
*patch* a bounded number of incidences.

**Status.** Paper proof (above; `geometry.tex` §3). Lean-checked: Theorem 1.2(a)–(c) for doubling with levels in
any graph (`Doubling.delorme_levelled`, `isBipartiteDegDiam_levelled`, `card_levelled_levels`), the hat lemma in both
directions for generalized polygons given as graphs of diameter $n$ and girth $2n$ with all degrees $\ge2$
(`Doubling.GenPolygonGraph.condC_iff_forestDiam`), and Corollary 1.4's "if" direction (`delorme_levelled_polygon`).

---

## 2. The fourth hat (diameter 3)

Araujo-Pardo and López [AL20] add three *hats* to $\mathrm{PG}(2,q)$ and obtain $n_b(q+2,3)\ge2(q^2+q+5)$. We add a
fourth.

### 2.1 Frame and notation

$\ell=[1:0:0]$ (the line $x=0$), $A=(1:0:0)\notin\ell$. The points of $\ell$ and the lines on $A$ are

$$X_t=(0:t:1),\ P=(0:1:0);\qquad \lambda_t=[0:1:-t],\ \lambda_\infty=[0:0:1]\qquad(t\in\mathbb F).$$

Every point is listed once among $A$, $X_t$ ($t\in\mathbb F$), $P$, $(x:y:1)$ ($x\ne0$), $(x:1:0)$ ($x\ne0$); every
line once among $\ell$, $\lambda_t$, $\lambda_\infty$, $[u:1:w]$ ($u\ne0$), $[1:0:w]$ ($w\ne0$). Facts used (one-line
computations):

- (F1) $\lambda_t\cap\ell=X_t$, $\lambda_\infty\cap\ell=P$; the points of $\lambda_t$ are $A$ and $(x:t:1)$,
  $x\in\mathbb F$ ($X_t$ at $x=0$); those of $\lambda_\infty$ are $A$ and $(x:1:0)$.
- (F2) The lines on $X_t$ are $\ell$ and $[w:1:-t]$, $w\in\mathbb F$ ($\lambda_t$ at $w=0$); the lines on $P$ are
  $\ell$, $\lambda_\infty$ and $[1:0:w]$, $w\ne0$.
- (F3) If $u=(x:y:z)$ with $x\ne0$, then $u$ and $X_s$ lie on $[(sz-y)/x:1:-s]\ne\ell$.
- (F4) A line $[u:v:w]$ with $u\ne0$ meets $\lambda_s$ in $(-(vs+w)/u:s:1)\ne A$; $[u:1:w]$ meets $\ell$ in
  $X_{-w}$.

Let $q\ge4$, $a,c\in\mathbb F\setminus\{0,1\}$ distinct, and

$$S=\{0,1,a,c\},\qquad T=\{0,1,c\},\qquad \sigma=(0\ c\ 1):\ 0\mapsto c\mapsto1\mapsto0.$$

### 2.2 Statement

**Definition 2.1.** $\mathcal S(q;a,c)$ has the points of $\mathrm{PG}(2,q)$ and five new points $Q,H_0,H_1,H_a,H_c$,
the lines of $\mathrm{PG}(2,q)$ and five new lines $M,K_0,K_1,K_a,K_c$, and exactly these incidences:

- (C1) every incidence of $\mathrm{PG}(2,q)$ except $X_s\,\mathrm I\,\lambda_s$ ($s\in S$), plus the *rotation*
  $X_0\,\mathrm I\,\lambda_c$, $X_c\,\mathrm I\,\lambda_1$, $X_1\,\mathrm I\,\lambda_0$ (that is $X_t\,\mathrm I\,\lambda_{\sigma(t)}$, $t\in T$);
- (C2) $H_s$ lies on $[w:1:-s]$ for every $w\in\mathbb F$ ($s\in S$): the lines on $X_s$ other than $\ell$;
- (C3) $K_s$ contains $(x:s:1)$ for every $x\in\mathbb F$ ($s\in S$): the points of $\lambda_s$ other than $A$;
- (C4) $M$ contains $P$, $X_t$ ($t\in\mathbb F\setminus T$), and $H_0,H_1,H_a,H_c$;
- (C5) $Q$ lies on $\lambda_\infty$, $\lambda_t$ ($t\in\mathbb F\setminus T$), and $K_0,K_1,K_a,K_c$;
- (C6) the *links* $A\,\mathrm I\,K_a$, $H_a\,\mathrm I\,\ell$, $H_0\,\mathrm I\,K_c$, $H_c\,\mathrm I\,K_1$, $H_1\,\mathrm I\,K_0$
  (that is $H_t\,\mathrm I\,K_{\sigma(t)}$, $t\in T$).

$G(q;a,c)$ is its incidence graph. $R(q;a,c)$ is $G(q;a,c)$ plus the *filler* edges

$$(x:y:1)\sim[x:1:-y]\quad(x\ne0,\ y\notin S),\qquad (x:1:0)\sim[1:0:-1/x]\quad(x\ne0).$$

**Theorem 2.2.** For every prime power $q\ge4$ and distinct $a,c\in\mathbb F\setminus\{0,1\}$, $G(q;a,c)$ and
$R(q;a,c)$ are bipartite, have $2(q^2+q+6)$ vertices, maximum degree $q+2$ and diameter 3, and $R(q;a,c)$ is
$(q+2)$-regular. Hence $n_b(q+2,3)\ge2(q^2+q+6)$, attained by a regular graph.

The construction and proof use only the axioms of a projective plane together with an anti-flag $(A,\ell)$ and four
points $X_s$ of $\ell$, so the coordinate-free version holds in every projective plane of order $q\ge3$
(`geometry.tex`, Theorem `thm:fourhat`); the regular completion in an arbitrary plane needs $q\ge7$ (Hall's theorem,
`geometry.tex`, remark "Arbitrary planes"). The hat pair $(H_s,K_s)$ is a copy of the flag $(X_s,\lambda_s)$ with the flag
"crossed", and $(Q,M)$ is a copy of the anti-flag $(A,\ell)$.

### 2.3 New vertices and every changed neighbourhood

| vertex | neighbours in $G(q;a,c)$ | degree |
|---|---|---|
| $Q$ | $\lambda_\infty$, $\lambda_t$ ($t\notin T$), $K_0,K_1,K_a,K_c$ | $q+2$ |
| $H_a$ | $[w:1:-a]$ ($w\in\mathbb F$), $M$, $\ell$ | $q+2$ |
| $H_t$, $t\in T$ | $[w:1:-t]$ ($w\in\mathbb F$), $M$, $K_{\sigma(t)}$ | $q+2$ |
| $M$ | $P$, $X_t$ ($t\notin T$), $H_0,H_1,H_a,H_c$ | $q+2$ |
| $K_a$ | $(x:a:1)$ ($x\in\mathbb F$), $Q$, $A$ | $q+2$ |
| $K_t$, $t\in T$ | $(x:t:1)$ ($x\in\mathbb F$), $Q$, $H_{\sigma^{-1}(t)}$ | $q+2$ |
| $A$ | $\lambda_t$ ($t\in\mathbb F$), $\lambda_\infty$, $K_a$ | $q+2$ |
| $P$ | $\ell$, $\lambda_\infty$, $[1:0:w]$ ($w\ne0$), $M$ | $q+2$ |
| $X_t$, $t\notin S$ | $\ell$, $[w:1:-t]$ ($w\in\mathbb F$), $M$ | $q+2$ |
| $X_a$ | $\ell$, $[w:1:-a]$ ($w\ne0$), $M$, $K_a$ | $q+2$ |
| $X_t$, $t\in T$ | $\ell$, $[w:1:-t]$ ($w\ne0$), $\lambda_{\sigma(t)}$, $K_t$ | $q+2$ |
| $(x:y:1)$, $x\ne0$ | $[u:1:-(ux+y)]$ ($u\in\mathbb F$), $[1:0:-x]$, and $K_y$ if $y\in S$ | $q+2$ if $y\in S$, else $q+1$ |
| $(x:1:0)$, $x\ne0$ | $\lambda_\infty$, $[1:-x:w]$ ($w\in\mathbb F$) | $q+1$ |
| $\ell$ | $P$, $X_t$ ($t\in\mathbb F$), $H_a$ | $q+2$ |
| $\lambda_\infty$ | $A$, $(x:1:0)$ ($x\in\mathbb F$), $Q$ | $q+2$ |
| $\lambda_t$, $t\notin S$ | $A$, $(x:t:1)$ ($x\in\mathbb F$), $Q$ | $q+2$ |
| $\lambda_a$ | $A$, $(x:a:1)$ ($x\ne0$), $Q$, $H_a$ | $q+2$ |
| $\lambda_t$, $t\in T$ | $A$, $(x:t:1)$ ($x\ne0$), $X_{\sigma^{-1}(t)}$, $H_t$ | $q+2$ |
| $[u:1:w]$, $u\ne0$ | $(x:-ux-w:1)$ ($x\in\mathbb F$), $(-1/u:1:0)$, and $H_{-w}$ if $-w\in S$ | $q+2$ if $-w\in S$, else $q+1$ |
| $[1:0:w]$, $w\ne0$ | $(-w:y:1)$ ($y\in\mathbb F$), $P$ | $q+1$ |

Here $\sigma^{-1}(0)=1$, $\sigma^{-1}(1)=c$, $\sigma^{-1}(c)=0$. This is the neighbourhood of *every* vertex. The
vertices of degree $q+1$ are the points $(x:y:1)$ ($x\ne0$, $y\notin S$), $(x:1:0)$ ($x\ne0$), and the lines
$[u:1:w]$ ($u\ne0$, $-w\notin S$), $[1:0:w]$ ($w\ne0$): $(q-1)(q-3)$ of each. The filler adds exactly one neighbour
to each of them.

### 2.4 Proof of Theorem 2.2

*Degrees (Lemma 2.3).* Each row of the table is (F1) or (F2) corrected by (C1)–(C6); within a row the listed
neighbours are distinct. For instance: $A$ keeps its $q+1$ lines and gains only $K_a$ ($A$ is not of the form
$(x:s:1)$); $X_a$ loses $\lambda_a$ and gains $M$ (as $a\notin T$) and $K_a$; $X_t$ ($t\in T$) loses $\lambda_t$ and
gains $\lambda_{\sigma(t)}$ and $K_t$, and is not on $M$; a point $(x:y:1)$ with $x\ne0$ is not on $\ell$, so it loses
nothing, and it gains $K_s$ iff $y=s\in S$; $Q$ is on $1+(q-3)+4=q+2$ lines; $H_s$ is on $q$ lines by (C2), on $M$,
and on exactly one link line. The line rows are the dual count: $\ell$ gains only $H_a$; $\lambda_a$ loses $X_a$ and
gains $Q$, $H_a$; $\lambda_t$ ($t\in T$) loses $X_t$, gains $X_{\sigma^{-1}(t)}$ and $H_t$; $[u:1:w]$ ($u\ne0$) gains
$H_s$ iff $s=-w\in S$; $M$ has $1+(q-3)+4$ points; $K_s$ has $q$ points, $Q$, and one link point. The filler map
$\delta:(x:y:z)\mapsto[x:z:-y]$ is a correlation of $\mathrm{PG}(2,q)$ ($ux+wz+(-v)(-y)=ux+vy+wz$), a point lies on
its image iff $x^2=0$, i.e. iff it is on $\ell$, and $\delta$ maps $(x:y:1)\mapsto[x:1:-y]$ and
$(x:1:0)\mapsto[x:0:-1]=[1:0:-1/x]$. So it is a bijection from the deficient points to the deficient lines, and the
filler edges are new (non-incident pairs). Hence $G$ has maximum degree $q+2$ and $R$ is $(q+2)$-regular.

*Reduction (Lemma 2.4).* If every line has a point, any two points are collinear and any two lines concurrent, the
incidence graph has diameter $\le3$: for an anti-flag $(p,L)$ take $p'\,\mathrm I\,L$ and a line $L'$ on $p,p'$; then
$p,L',p',L$ is a path. (Lemma 0.1(ii).)

In the next two lemmas "incident" means incident in $\mathcal S(q;a,c)$. The only incidences of $\mathrm{PG}(2,q)$
missing are $X_s\,\mathrm I\,\lambda_s$, $s\in S$; so a plane incidence $u\,\mathrm I\,L$ survives whenever $u\notin\ell$
or $L$ is not on $A$.

*Points (Lemma 2.5).* Any two points $u\ne v$ are collinear.

- (P1) Both in $\mathrm{PG}(2,q)$, $L=uv$. If both incidences survive, use $L$. Otherwise, say $u=X_s$, $L=\lambda_s$,
  $s\in S$, and $v=A$ or $v=(x:s:1)$, $x\ne0$. If $v=(x:s:1)$: $K_s$. If $v=A$, $s=a$: $K_a$ (C3, C6). If $v=A$,
  $s\in T$: $\lambda_{\sigma(s)}$ (rotation).
- (P2) $Q$ and $u$. $u\in\{A,P\}$ or $u=(x:1:0)$: $\lambda_\infty$. $u=X_t$, $t\notin S$: $\lambda_t$. $u=X_s$,
  $s\in S$: $K_s$. $u=(x:y:1)$, $x\ne0$: $\lambda_y$ if $y\notin T$, $K_y$ if $y\in T$.
- (P3) $H_s$ and $u$. $u\notin\ell$ (including $A$): the line of (F3), which contains $H_s$ by (C2). $u=X_s$:
  $[1:1:-s]$. $u=P$ or $u=X_t$, $t\notin T$, $t\ne s$: $M$. $u=X_t$, $t\in T\setminus\{s\}$, $s=a$: $\ell$.
  $u=X_t$, $t\in T\setminus\{s\}$, $s\in T$: as $\sigma$ is a 3-cycle, $t=\sigma(s)$ or $t=\sigma^{-1}(s)$; use
  $K_{\sigma(s)}$ (contains $X_{\sigma(s)}$ and $H_s$) or $\lambda_s$ (contains $X_{\sigma^{-1}(s)}$ by the rotation,
  and $H_s$ by (C2) with $w=0$).
- (P4) Two new points. $H_s,H_{s'}$: $M$. $Q,H_a$: $\lambda_a$. $Q,H_t$ ($t\in T$): $K_{\sigma(t)}$.

*Lines (Lemma 2.6).* Any two lines $L\ne N$ are concurrent.

- (Λ1) Both in $\mathrm{PG}(2,q)$, $p=L\cap N$. If both incidences survive, use $p$. Otherwise, say $p=X_s$,
  $L=\lambda_s$, and $N=\ell$ or $N=[w:1:-s]$, $w\ne0$. If $N=[w:1:-s]$: $H_s$. If $N=\ell$, $s=a$: $H_a$. If
  $N=\ell$, $s\in T$: $X_{\sigma^{-1}(s)}$ (rotation).
- (Λ2) $M$ and $L$. $L$ on $P$ ($L=\ell,\lambda_\infty$ or $[1:0:w]$): $P$. $L=\lambda_t$, $t\notin S$: $X_t$.
  $L=\lambda_s$, $s\in S$: $H_s$. $L=[u:1:w]$, $u\ne0$: it meets $\ell$ in $X_r$, $r=-w$ (F4); use $X_r$ if
  $r\notin T$, and $H_r$ if $r\in T$ ($H_r$ is on $[u:1:-r]$ and on $M$).
- (Λ3) $K_s$ and $L$. $L$ not on $A$ ($L=\ell$ or $[u:v:w]$, $u\ne0$): $L\cap\lambda_s=(x:s:1)$ (F1, F4), which is on
  $K_s$, and its incidence with $L$ survives. $L=\lambda_s$: $(1:s:1)$. $L=\lambda_\infty$ or $\lambda_t$, $t\notin T$:
  $Q$. $L=\lambda_t$, $t\in T\setminus\{s\}$, $s=a$: $A$. $L=\lambda_t$, $t\in T\setminus\{s\}$, $s\in T$: if
  $t=\sigma(s)$, $X_s$ (on $\lambda_{\sigma(s)}$ and $K_s$); if $t=\sigma^{-1}(s)$, $H_t$ (on $\lambda_t$ and on
  $K_{\sigma(t)}=K_s$).
- (Λ4) Two new lines. $K_s,K_{s'}$: $Q$. $M,K_a$: $X_a$. $M,K_t$ ($t\in T$): $H_{\sigma^{-1}(t)}$.

*Conclusion.* By Lemmas 2.4–2.6, $G$ has diameter $\le3$; adding the filler cannot increase it (Lemma 0.2). The
graphs are bipartite and not complete bipartite ($A\notin\ell$), so the diameter is exactly 3. $\square$

(The proof uses only that $\mathbb F$ is a field and $0,1,a,c$ are distinct. The correlation $\delta$, extended by
$H_s\leftrightarrow K_s$, $Q\leftrightarrow M$, maps $\mathcal S(q;a,c)$ with $\sigma$ onto the dual of the
structure built with $\sigma^{-1}$, so Lemma 2.6 is also Lemma 2.5 for $\sigma^{-1}$; we wrote both out so that every
case can be checked directly.)

**Remark 2.7 (the three-hat structure of [AL20] in these coordinates).** Hats $S_{AL}=\{0,1,a\}$, no rotation, only
the flag $(X_a,\lambda_a)$ removed, links $A\,\mathrm I\,K_a$, $H_a\,\mathrm I\,\ell$, $H_0\,\mathrm I\,K_1$,
$H_1\,\mathrm I\,K_0$; $M$ contains $P$ and $X_t$ ($t\ne0,1$); $Q$ lies on $\lambda_\infty$ and $\lambda_t$
($t\ne0,1$). Dictionary with the affine coordinates of [AL20]: $(x,y)=(x:y:1)$, $[m,b]=[m:-1:b]$,
$L_c=[1:0:-c]$, $L=[0:0:1]$, $P_m=(1:m:0)$; so $L_0=\ell$, $P_0=A$, $(0,s)=X_s$, $[0,s]=\lambda_s$,
$L=\lambda_\infty$. The completing matching printed in [AL20] is $(x,y)\sim[x,y]$ ($x\ne0$, $y\notin S_{AL}$) and
$P_i\sim L_i$ for $i\in\mathbb F\setminus\{0,1,a\}$; with this index set $P_1,P_a,L_1,L_a$ keep degree $q+1$. With
$i\in\mathbb F^*$ the graph is $(q+2)$-regular, as intended. This does not affect the maximum degree or the diameter.

**Cells.** $q=9,11,13$ give $(11,3)$: $192$ (2013: 190), $(13,3)$: $276$ (2013: 270; wiki 274 [AL20]), $(15,3)$:
$376$ (2013: 370; wiki 374 [AL20]), all regular. At $q=5$ it gives $72<80=n_b(7,3)$ (optimal value known).

**Status.** Paper proof (above; `coords.tex`; coordinate-free in `geometry.tex` §4). Computer-checked:
`research/plus2/coords/coords.py` builds the structure three ways (from (C1)–(C6), from the point rows and from the
line rows of the table), checks they agree, and checks degrees, both covering properties and the exact diameter of
$G$ and $R$ for every prime power $q\le13$ and every admissible $(a,c)$; removing the rotation or the link
$H_1\,\mathrm I\,K_0$ gives diameter 4 in every case tested. Lean-checked: the regular version for every finite
projective plane of order $q\ge4$ with a chosen frame (`Plus2.plus2_regular`, `plus2_regular_of_order`), and the three
record graphs (`nb_11_3`, `nb_13_3`, `nb_15_3`); see Section 9.

