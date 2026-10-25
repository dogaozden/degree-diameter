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

1. **The 2013 baseline at $D=3$.** The README and the values table of `geometry.tex` list $(13,3)=274$ and
   $(15,3)=374$ as "table" values. Those are the later values of Araujo-Pardo and López [AL20] (Graphs Combin. 2022).
   The 2013 survey table (Miller–Širáň, Electron. J. Combin. DS14v2, Table 4) has $270$ and $370$ there. Both columns
   are now shown, here and in `geometry.tex` (Table 4).
   Provenance of the current values: the wiki was read on 2026-10-10 for $(7,4)$, $(7,5)$, $(11,3)$, $(11,4)$,
   $(13,3)$, $(15,3)$ (`records/bipartite_dd/CANDIDATES.md`), and the 2026-10-20 proofread reports the `geometry.tex`
   table values as matching the wiki; later sessions could not reach the wiki, and this note did not re-check it
   (`research/frontier/TABLE.md`). Apart from $(13,3)$ and $(15,3)$ we know of no change since 2013 in the cells below.
2. **Corollary C1 needs no Klein correspondence.** `NOTE.md` derived the $(16,4)$ graph through $Q(4,q)$ and listed
   the Klein step as not formalised. The same construction is the point–line dual one in $W(3,q)$ itself: one copy of
   each point of the Singer 2-ovoid and two copies of each line of a regular spread (Section 5). We checked this form
   by computer for $q=3,5$ (`research/theorems/polish/c1w3.py`: orders 120 and 416, diameter 4).
3. **Lean status in `NOTE.md` §7 is out of date.** Theorem B *with* stand-ins is now in Lean (`GQST.standin_gqst`),
   and so are the regular versions; see Section 9.
4. **`NOTE.md` open problem 3** ($q^2+1$ shadow lines on $Q(4,q)$ with one ovoid of clones, $q$ odd) is settled
   negatively by `geometry.tex`, Proposition 5.13 (at most $q^2-q+2$). `NOTE.md` is superseded on this point.
5. **Theorem A in nicer coordinates.** The pair $\kappa_1=1/2$, $\kappa_2=1/(2\varepsilon)$ satisfies
   $\kappa_1\kappa_2=1/(4\varepsilon)$, so the two quadrics can be written $2X_0X_1=X_2^2-\varepsilon X_3^2$ and
   $2\varepsilon X_0X_1=X_2^2-\varepsilon X_3^2$. Same theorem; checked by computer for $q=3,5,7,9$ (`polish/thmA.py`).
6. **The fourth hat needs $q\ge3$ without coordinates and $q\ge4$ in coordinates.** The coordinate-free statement
   uses four points of a line ($q+1\ge4$); the coordinate version labels them by four field elements $0,1,a,c$
   ($q\ge4$). Both are stated as such below; no table cell has $q=3$.
7. **Delorme's two 1985 papers.** Which of [D85a] and [D85b] contains the doubling with levels and the $D=4,6$ table
   constructions is not confirmed (we have not seen the full texts). Both are cited. Tallini's page range (Mitt. Math. Sem.
   Giessen 201 (1991) 141–147), marked "to be verified" in `geometry.tex`, agrees with independent citing papers and
   is now given without the caveat. The 2013 values at $\Delta=16$ (5134 at $D=4$, 884062 at $D=6$) are Delorme's
   doublings with $m=3$; this is now stated (Example 3.4, Remark 6.9).
8. **Theorem R is explicit except for the completing anti-flags.** The completion step is an existence argument
   (Lemma 7.2). We now say this plainly: every neighbourhood is listed except the $(m-1)$ completing anti-flags at the
   deficient vertices, and neither the maximum degree nor the diameter depends on that choice.
9. **Printed matching in [AL20].** Already noted in `geometry.tex`: with the index set $\mathbb F\setminus\{0,1,a\}$
   four vertices keep degree $q+1$; with $\mathbb F^*$ the graph is $(q+2)$-regular as intended. Kept (Remark 2.7).
10. **Regular fourth hat in arbitrary planes.** `geometry.tex` Remark 4.8 obtained a regular completion in a
   non-Desarguesian plane only for $q\ge7$. The count used in the Lean proof (each deficient element is incident with
   exactly $q-4$ deficient elements) gives it for every $q\ge4$ (Section 2.2). The Lean theorem already says so.
11. **Credit to [ADFL21].** `geometry.tex` did not cite Araujo-Pardo–Dalfó–Fiol–López (line doubling in a GQ, the
   closest prior use of line copies); it does now, and so does Section 3 here.
12. **`geometry.tex` revised to match** (25 October): the 2013 column, the coordinate tables and remarks of this note,
   the explicit deletion in Theorem R, a Verification section (what Lean covers) and the $(7,4)$ appendix. Theorem
   numbers below refer to the revised, recompiled `geometry.pdf`.

## Summary of cells

$M_b$ is the bipartite Moore bound. "2013" is the survey table [MS13] (DS14v2, Table 4, as of March 2013); "wiki" is
the current CombinatoricsWiki value [CW], shown only where we know it differs from 2013 (see Change 1 for what was
checked). All our graphs were rebuilt and checked by the coordinator.

| $(\Delta,D)$ | $M_b$ | 2013 | wiki | ours | regular? | result | status |
|------|------:|------:|-----:|-------:|--------|------------------------------|----------------|
| (11,3) | 222 | 190 | | **192** | yes | fourth hat, $q=9$ | paper, computer, Lean |
| (13,3) | 314 | 270 | 274 | **276** | yes | fourth hat, $q=11$ | paper, computer, Lean |
| (15,3) | 422 | 370 | 374 | **376** | yes | fourth hat, $q=13$ | paper, computer, Lean |
| (7,4) | 518 | 346 | | **359** | no (350 regular) | Theorem B on $Q(4,5)$, explicit example | computer, Lean (graph) |
| (11,4) | 2222 | 1734 | | **1782** | yes | Theorem A, $q=9$ | paper, computer, Lean |
| (13,4) | 3770 | 3064 | | **3146** | yes | Theorem A, $q=11$ | paper, computer, Lean |
| (15,4) | 5910 | 4946 | | **5070** | yes | Theorem A, $q=13$ | paper, computer, Lean |
| (16,4) | 7232 | 5134 | | **5440** | yes | Prop. C + Cor. C1, $q=13$ | paper, computer, Lean |
| (7,5) | 3110 | 1134 | | **1152** | yes | Haar lemma, $S_4\times\mathbb Z_{24}$ | paper, computer, Lean |
| (9,5) | 9362 | 2496 | | **2662** | yes | Haar lemma, Heisenberg group mod 11 | paper, computer, Lean |
| (7,6) | 18662 | 8992 | | **9592** | 9348 | Theorem D / R, $q=5$ | paper, computer, Lean |
| (11,6) | 222222 | 142464 | | **148944** | 147500 | Theorem D / R, $q=9$ | paper, computer, Lean (theorem) |
| (13,6) | 542906 | 374452 | | **388972** | 386328 | Theorem D / R, $q=11$ | paper, computer, Lean (theorem) |
| (15,6) | 1158390 | 842048 | | **870440** | 866068 | Theorem D / R, $q=13$ | paper, computer, Lean (theorem) |
| (16,6) | 1627232 | 884062 | | **940846** | 927724 | Theorem D / R, $q=13$, $m=3$ | paper, computer, Lean (theorem) |

"Lean (theorem)": the general theorem is Lean-checked for every $q$, so these orders are Lean-checked lower bounds
(Section 9); the graphs themselves are too large for a kernel certificate. "Lean (graph)": the specific graph is
kernel-checked. The 2013 values at $D=4$ and $D=6$ are Delorme's [D85a, D85b], with $\Delta=q+m$: $m=2$ at
$\Delta=7,11,13,15$ ($2q^3+3q^2+3q+6$ at $D=4$; $2(q+1)(q^4+q^2+1)+q^4+4q^3+q^2+4q+10$ at $D=6$) and $m=3$, $q=13$ at
$\Delta=16$ (5134 and 884062); see Example 3.4 and Remark 6.9. At $(8,5)$ the Haar lemma
gave $1764>1710$ (Lean-checked), since superseded by a $2048$-vertex lift that is not covered here.

---

## 0. Conventions

An *incidence structure* $\mathcal S=(\mathcal P,\mathcal L,\mathrm I)$ has points, lines and a symmetric incidence
relation; repeated points and repeated lines (same incidences) are allowed. Its *incidence graph* $\Gamma(\mathcal S)$ has vertex set
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

So pure doubling gains at most $2(m-1)$ elements in a projective plane (2 for $m=2$); the hats of Section 2 double flags and then
*patch* a bounded number of incidences.

**Status.** Paper proof (above; `geometry.tex` §3). Lean-checked, for any finite graph: Theorem 1.2(a)–(c) under
(L0), (L1) and (C$_D$) together, with the degree bound $\Delta+m-1$ (the "equality only if" clause of (b) and part (d)
are not formalised) (`Doubling.delorme_levelled`, `isBipartiteDegDiam_levelled`, `card_levelled_levels`), the hat lemma in both
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
(`geometry.tex`, Theorem 4.2), and so does a regular completion, for every $q\ge4$: a deficient point $p$ lies on
exactly $q-4$ deficient lines (the lines on $p$ other than $Ap$ meet $\ell$ in the $q$ points other than $Ap\cap\ell$,
four of which are the $X_s$), dually a deficient line has exactly $q-4$ deficient points, and $2(q-4)\le(q-1)(q-3)$,
so Hall's theorem gives a perfect matching of non-incident deficient pairs (this is the argument of the Lean proof;
`geometry.tex` Remark 4.8 had the weaker bound $q+1$ and so needed $q\ge7$). The hat pair $(H_s,K_s)$ is a copy of the flag $(X_s,\lambda_s)$ with the flag
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

- (N1) Both in $\mathrm{PG}(2,q)$, $p=L\cap N$. If both incidences survive, use $p$. Otherwise, say $p=X_s$,
  $L=\lambda_s$, and $N=\ell$ or $N=[w:1:-s]$, $w\ne0$. If $N=[w:1:-s]$: $H_s$. If $N=\ell$, $s=a$: $H_a$. If
  $N=\ell$, $s\in T$: $X_{\sigma^{-1}(s)}$ (rotation).
- (N2) $M$ and $L$. $L$ on $P$ ($L=\ell,\lambda_\infty$ or $[1:0:w]$): $P$. $L=\lambda_t$, $t\notin S$: $X_t$.
  $L=\lambda_s$, $s\in S$: $H_s$. $L=[u:1:w]$, $u\ne0$: it meets $\ell$ in $X_r$, $r=-w$ (F4); use $X_r$ if
  $r\notin T$, and $H_r$ if $r\in T$ ($H_r$ is on $[u:1:-r]$ and on $M$).
- (N3) $K_s$ and $L$. $L$ not on $A$ ($L=\ell$ or $[u:v:w]$, $u\ne0$): $L\cap\lambda_s=(x:s:1)$ (F1, F4), which is on
  $K_s$, and its incidence with $L$ survives. $L=\lambda_s$: $(1:s:1)$. $L=\lambda_\infty$ or $\lambda_t$, $t\notin T$:
  $Q$. $L=\lambda_t$, $t\in T\setminus\{s\}$, $s=a$: $A$. $L=\lambda_t$, $t\in T\setminus\{s\}$, $s\in T$: if
  $t=\sigma(s)$, $X_s$ (on $\lambda_{\sigma(s)}$ and $K_s$); if $t=\sigma^{-1}(s)$, $H_t$ (on $\lambda_t$ and on
  $K_{\sigma(t)}=K_s$).
- (N4) Two new lines. $K_s,K_{s'}$: $Q$. $M,K_a$: $X_a$. $M,K_t$ ($t\in T$): $H_{\sigma^{-1}(t)}$.

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
record graphs (`nb_11_3`, `nb_13_3`, `nb_15_3`). The Lean incidence relation (`Plus2.Frame.inc`) is
Definition 2.1 in coordinate-free form, rule for rule: the same rotation $X_t\,\mathrm I\,\lambda_{\sigma(t)}$, links,
$M$, $Q$, $H_s$ and $K_s$ (we compared them for this note). See Section 9.

---

## 3. Theorem B: clones and shadow lines in a generalized quadrangle

A *generalized quadrangle* (GQ) of order $(s,t)$, $s,t\ge1$, has $(s+1)(st+1)$ points and $(t+1)(st+1)$ lines, and
for every anti-flag $(p,L)$ exactly one point of $L$ is collinear with $p$. Its incidence graph has diameter 4.
Copies of lines in a GQ appear already in Araujo-Pardo, Dalfó, Fiol and López [ADFL21, Sec. 4], who double every line
to get biregular graphs (semi-double graphs). Theorem B copies only some lines, with weights, lets a copy attach to
clones (stand-ins), and combines this with weighted point copies in the spirit of Delorme–Farhi duplication [DF84].

### 3.1 Statement

**Definition 3.1 (clones and shadows).** Let $\mathcal S=(\mathcal P,\mathcal L)$ be a GQ of order $(s,t)$, let
$w:\mathcal P\to\mathbb Z_{\ge0}$ be a weight, and $\mathcal M$ a finite multiset of lines. For each entry $\mu$ of
$\mathcal M$, with underlying line $L_\mu$, choose for every point $p\,\mathrm I\,L_\mu$ a *stand-in*
$\sigma_\mu(p)\in\{p,p^1,\dots,p^{w(p)}\}$. The structure $\mathcal S[w,\mathcal M,\sigma]$ has

- points: $\mathcal P$ and the *clones* $p^1,\dots,p^{w(p)}$ of each $p\in\mathcal P$;
- lines: $\mathcal L$ and one *shadow line* $L^\mu$ for each entry $\mu$ of $\mathcal M$;
- incidences: those of $\mathcal S$; $p^i\,\mathrm I\,L$ whenever $p\,\mathrm I\,L\in\mathcal L$; and
  $\sigma_\mu(p)\,\mathrm I\,L^\mu$ for $p\,\mathrm I\,L_\mu$.

**New vertices and changed neighbourhoods.**

| vertex | neighbours | degree |
|---|---|---|
| clone $p^i$ | the $t+1$ old lines on $p$; the shadow lines $L^\mu$ with $\sigma_\mu(p)=p^i$ | $t+1+\#\{\mu:\sigma_\mu(p)=p^i\}$ |
| shadow line $L^\mu$ | $\sigma_\mu(p)$ for the $s+1$ points $p$ of $L_\mu$ | $s+1$ |
| old point $p$ | its $t+1$ lines; the shadow lines $L^\mu$ with $\sigma_\mu(p)=p$ | $t+1+\#\{\mu:\sigma_\mu(p)=p\}$ |
| old line $L$ | its $s+1$ points and all their clones | $s+1+\sum_{p\,\mathrm I\,L}w(p)$ |

When all stand-ins are old points ($\sigma=\mathrm{id}$), a shadow line is adjacent exactly to the old points of
$L_\mu$, and clones are adjacent only to old lines.

**Theorem 3.2 (Theorem B).** Let $\mathcal S$ be a GQ of order $(s,t)$, $s,t\ge1$, and
$\mathcal S'=\mathcal S[w,\mathcal M,\sigma]$.

- (a) $\mathcal S'$ has diameter 4.
- (b) $\mathcal S'$ has maximum degree $\le\Delta$ iff $\Delta\ge\max(s,t)+1$, $\sum_{p\,\mathrm I\,L}w(p)\le\Delta-s-1$
  for every line $L$ of $\mathcal S$, and every point of $\mathcal S'$ (old point or clone) is a stand-in for at most
  $\Delta-t-1$ entries of $\mathcal M$.
- (c) $\mathcal S'$ has $(s+1)(st+1)+\sum_pw(p)$ points and $(t+1)(st+1)+|\mathcal M|$ lines.

### 3.2 Proof

(b) and (c) are read off the table. (a) Write $\pi$ for the map sending a clone or shadow line to its underlying point
or line. Every point $x$ of $\mathcal S'$ is incident with every old line through $\pi(x)$. We use Lemma 0.1(i); no
element is isolated. Let $(x,Y)$ be an anti-flag of $\mathcal S'$.

- $Y$ old. Then $\pi(x)\notin Y$ (else $x\,\mathrm I\,Y$). Let $r$ be the point of $Y$ collinear with $\pi(x)$, on
  the line $N$. Then $x\,\mathrm I\,N\,\mathrm I\,r\,\mathrm I\,Y$.
- $Y=L^\mu$, $\pi(x)\notin L_\mu$. Let $r\,\mathrm I\,L_\mu$ be collinear with $\pi(x)$, on the line $N$. Then
  $x\,\mathrm I\,N\,\mathrm I\,\sigma_\mu(r)\,\mathrm I\,L^\mu$.
- $Y=L^\mu$, $\pi(x)\,\mathrm I\,L_\mu$. Pick $r\,\mathrm I\,L_\mu$, $r\ne\pi(x)$ ($s\ge1$). Then
  $x\,\mathrm I\,L_\mu\,\mathrm I\,\sigma_\mu(r)\,\mathrm I\,L^\mu$.

So $d(x,Y)\le3$ for every anti-flag, and the diameter is $\le4$. Two non-collinear old points (they exist, since a
point is collinear with $s(t+1)<(s+1)(st+1)-1$ others) stay non-collinear: they share no old line, a shadow line
$L^\mu$ contains only points over points of $L_\mu$, and an old point lies over itself only. So the diameter is 4.
$\square$

**Corollary 3.3 (exact weights).** Let $\Delta\ge\max(s,t)+1$, and suppose $w$ is a weighted
$(\Delta-s-1)$-ovoid ($\sum_{p\,\mathrm I\,L}w(p)=\Delta-s-1$ for every line) and $\mathcal M$ a weighted
$(\Delta-t-1)$-cover (every point on exactly $\Delta-t-1$ entries). Then $\mathcal S[w,\mathcal M,\mathrm{id}]$ has
diameter 4, maximum degree $\Delta$ and $2\Delta(st+1)$ elements. It becomes $\Delta$-regular, with the same order
and diameter 4, by the following explicit flags: number the clones $c_0,c_1,\dots$ and the shadow lines
$y_0,\dots,y_{b-1}$ ($b=|\mathcal M|$), put $k=\Delta-t-1$, and join $c_i$ to $y_j$ for
$j\equiv ik,ik+1,\dots,ik+k-1\pmod b$.

*Proof.* Double counting flags gives $\sum_pw(p)=(\Delta-s-1)(st+1)$ and $|\mathcal M|=(\Delta-t-1)(st+1)$; the
total is $(s+t+2+\Delta-s-1+\Delta-t-1)(st+1)=2\Delta(st+1)$. Old points and lines have degree $\Delta$, clones
$t+1$, shadow lines $s+1$. The added pairs are anti-flags (with $\sigma=\mathrm{id}$ no clone is on a shadow line);
the blocks $\{ik,\dots,ik+k-1\}$, $i=0,1,\dots$, run through $0,1,\dots,k\sum_pw(p)-1=b(\Delta-s-1)-1$, so modulo $b$
every residue is hit exactly $\Delta-s-1$ times, and within a block the residues are distinct as $k\le b$. Adding
flags does not increase distances, and two non-collinear old points still share no line. $\square$

**Example 3.4 (Delorme's $D=4$ construction [D85a, D85b], the 2013 values).** In $W(q)$ take a spread $\Sigma$, a
line $v\in\Sigma$, and $\mathcal A_1=\{v\}$, $\mathcal A_0=\Sigma\cup\{\text{points of }v\}$. (L1): the elements on $v$
are its points; a point of $v$ meets only $v$ in $\mathcal A_1$, a line of $\Sigma\setminus\{v\}$ nothing. (L0): a
point off $v$ is on exactly one line of $\Sigma$ and on no other line of $\mathcal A_0$; a line not in $\Sigma$ has at
most one point on $v$. The components are the star $v\cup\{\text{points of }v\}$ and single lines, so (C$_4$) holds
(Lemma 1.3). Theorem 1.2 gives maximum degree $q+m$, diameter 4 and
$2(q+1)(q^2+1)+(m-1)\bigl((q^2+1)+(q+1)+m\bigr)$ elements. For $m=2$ this is $2q^3+3q^2+3q+6$: 346, 1734, 3064,
4946 at $q=5,9,11,13$; for $m=3$, $q=13$ it is $4760+2\cdot187=5134$, the 2013 value at $\Delta=16$.

**Remark 3.5 (limit of shadow lines on $Q(4,q)$, `geometry.tex` Prop. 5.13).** For $q$ odd, an ovoid
$\mathcal O$ of $Q(4,q)$, $w=\mathbf 1_{\mathcal O}$ and maximum degree $q+2$, at most $q^2-q+2$ shadow lines are
possible: every old point and clone serves at most one shadow line, so a point off $\mathcal O$ is on at most one entry
of $\mathcal M$ and a point of $\mathcal O$ on at most two; if some $o\in\mathcal O$ is on two entries, each other entry
$L$ misses $o$ and so has a unique point $y$ collinear with $o$; $y\notin\mathcal O$ (points of an ovoid are
pairwise non-collinear); the line $oy$ is not an entry of $\mathcal M$ (else $y\notin\mathcal O$ would be on two
entries), so it is one of the $q-1$ lines on $o$ other than the two entries through $o$, and $y$ is one of its $q$
points other than $o$; distinct $L$ give distinct $y$. So $|\mathcal M|\le2+q(q-1)$. Otherwise $\mathcal M$ is a
partial spread and $|\mathcal M|\le q^2-q+1$ (Tallini [Tal91]; see also [CDPS22], §1).

**Application: $(7,4)\ge359$.** $Q(4,5)$, one clone of each point of an elliptic-quadric ovoid ($w=\mathbf 1_{\mathcal O}$),
and 21 shadow lines with stand-ins: $2\cdot6\cdot26+26+21=359$, maximum degree 7. Such examples come from an integer
program (HiGHS proves 21 optimal for this family; `research/gq4x/q4_share_ilp.py`, earlier optimum in
`research/gq4x/graphs/q4_share_q5_n359.json`); they are not members of a proved infinite family. The record file
`records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json` (found by evolutionary search) decomposes the same way after
deleting 21 redundant edges, with stand-ins essential. Every ovoid of $Q(4,p)$, $p$ prime, is an elliptic quadric
[BGS06], so the choice of ovoid does not matter. Appendix A lists, in coordinates, an optimum of the same integer
program re-solved for this note (a different set of 21 lines from the earlier file), so that such a graph can be
checked by hand. Cell: $(7,4)$, 2013: 346, ours 359 (regular: 350 from Theorem A at $q=5$).

**Status.** Paper proof (above; `NOTE.md` §2, `geometry.tex` Theorem 5.4). Computer-checked on many instances
(`research/gq4`, `research/gq4x`). Lean-checked for every GQ of order $(s,t)$: the version with all stand-ins original
and arbitrary point and line multiplicities (`GQST.gqst`), the version with stand-ins (`GQST.standin_gqst`), and the
regular completion (`GQST.regular_copy_graph`); the 359 graph itself (`nb_7_4`). See Section 9.

---

## 4. Theorem A: the Ahrens–Szekeres quadrangle and two elliptic quadrics

### 4.1 Coordinates

Let $q$ be odd. $W(q)=W(3,q)$ is the symplectic quadrangle of $\mathrm{PG}(3,q)$ for the alternating form
$\beta(u,v)=u_0v_1-u_1v_0+u_2v_3-u_3v_2$. Let $x=(1:0:0:0)$; then $x^\perp$ is the plane $X_1=0$. Payne's derived
quadrangle $\mathrm{AS}(q)=P(W(q),x)$ [P71], [PT, 3.1.4] has

- **points**: the $q^3$ points $(a:1:b:c)$, $a,b,c\in\mathbb F$ (the points off $x^\perp$); write
  $(a,w)$ with $w=(b,c)$;
- **lines of type (i)** (*fibres*), $q^2$ of them: $\{(a_0+\mu:1:w_0):\mu\in\mathbb F\}$, the line
  $\langle x,(a_0:1:w_0)\rangle$ minus $x$;
- **lines of type (ii)**, $q^2(q+1)$ of them: for a point $(a_0:1:w_0)$ and a direction $d=(d_1:d_2)\in\mathrm{PG}(1,q)$,
  $$\ell(a_0,w_0;d)=\{(a_0+\lambda\rho:1:w_0+\lambda d):\lambda\in\mathbb F\},\qquad \rho=\det(w_0,d)=b_0d_2-c_0d_1,$$
  the totally isotropic line through $(a_0:1:w_0)$ and $(\rho:0:d_1:d_2)$, minus the latter point.

(Check: $\beta((a_0,1,b_0,c_0),(\rho,0,d_1,d_2))=-\rho+b_0d_2-c_0d_1=0$. A point off $x^\perp$ is on $q+1$ totally
isotropic lines, none through $x$, each meeting $x^\perp$ in one point $(\rho:0:d)$, $d\ne0$; so each point of
$\mathrm{AS}(q)$ is on one fibre and $q+1$ lines of type (ii), and every line has $q$ points.) $\mathrm{AS}(q)$ is a GQ
of order $(q-1,q+1)$ [P71], [PT, 3.1.4, 3.2.6]; for $q$ odd it is the Ahrens–Szekeres quadrangle [AS69]. The fibres
form a spread.

Fix a non-square $\varepsilon\in\mathbb F$ and put $N(b,c)=b^2-\varepsilon c^2$ (anisotropic: $N(w)=0$ only for
$w=0$). For $\kappa\in\mathbb F^*$ let $\mathcal E_\kappa$ be the quadric $X_0X_1=\kappa N(X_2,X_3)$. It is elliptic
(a hyperbolic pair plus an anisotropic binary form), passes through $x$ with tangent plane $x^\perp$, and
$\mathcal E_\kappa\setminus\{x\}=\{(\kappa N(w):1:w):w\in\mathbb F^2\}$ is a set of $q^2$ points of $\mathrm{AS}(q)$,
one on each fibre.

### 4.2 Statement

**Theorem 4.1 (Theorem A).** Let $q$ be odd, $\varepsilon$ a non-square and $\kappa_1\kappa_2=1/(4\varepsilon)$.
Every line of $\mathrm{AS}(q)$ meets $\mathcal E_{\kappa_1}\setminus\{x\}$ and $\mathcal E_{\kappa_2}\setminus\{x\}$
in exactly two points in total (a point in both counted twice). The two quadrics meet only in $x$ and
$e=(0:1:0:0)$. So $\varpi=\mathbf 1_{\mathcal E_{\kappa_1}\setminus x}+\mathbf 1_{\mathcal E_{\kappa_2}\setminus x}$ is a
weighted 2-ovoid of $\mathrm{AS}(q)$, with $\varpi(e)=2$ and $\varpi\in\{0,1\}$ elsewhere.

The choice $\kappa_1=\tfrac12$, $\kappa_2=\tfrac1{2\varepsilon}$ gives the two quadrics

$$\mathcal E_1:\ 2X_0X_1=X_2^2-\varepsilon X_3^2,\qquad \mathcal E_2:\ 2\varepsilon X_0X_1=X_2^2-\varepsilon X_3^2 .$$

**Corollary 4.2 (Corollary A1).** For every odd prime power $q$, adjoining to $\mathrm{AS}(q)$ one clone of each
point of $\mathcal E_1\setminus\{x\}$ and one of each point of $\mathcal E_2\setminus\{x\}$ (so $e$ gets two clones)
gives a $(q+2)$-regular incidence structure of diameter 4 with $2q^2(q+2)$ elements. Hence
$n_b(q+2,4)\ge2q^2(q+2)$.

**New vertices.** For $P=(\kappa_iN(w):1:w)\in\mathcal E_i\setminus\{x\}$ ($i=1,2$, $w\in\mathbb F^2$), the clone
$P^{(i)}$ is adjacent exactly to the $q+2$ lines of $\mathrm{AS}(q)$ through $P$: the fibre
$\{(\kappa_iN(w)+\mu:1:w):\mu\in\mathbb F\}$ and, for each $d\in\mathrm{PG}(1,q)$, the line
$\ell(\kappa_iN(w),w;d)$. The two clones of $e$ are adjacent to the same $q+2$ lines. Changed old neighbourhoods: the
fibre over $w_0$ gains the clones of $(\kappa_1N(w_0):1:w_0)$ and $(\kappa_2N(w_0):1:w_0)$; the line
$\ell(a_0,w_0;d)$ gains the clones of its points on $\mathcal E_1$ and on $\mathcal E_2$, which are given by the roots
$\lambda$ of the quadratic $(\star)$ below with $\kappa=\kappa_1,\kappa_2$ (two clones in total). Old points are
unchanged. Every vertex has degree $q+2$.

### 4.3 Proof

*Fibres.* The fibre over $w_0$ meets $\mathcal E_\kappa$ only at $\mu=\kappa N(w_0)-a_0$: one point of each quadric.

*Lines of type (ii).* Let $B=N(w_0+d)-N(w_0)-N(d)=2(b_0d_1-\varepsilon c_0d_2)$. The point with parameter $\lambda$
of $\ell(a_0,w_0;d)$ lies on $\mathcal E_\kappa$ iff $a_0+\lambda\rho=\kappa N(w_0+\lambda d)$, i.e.

$$\kappa N(d)\lambda^2+(\kappa B-\rho)\lambda+\kappa N(w_0)-a_0=0. \tag{$\star$}$$

As $N(d)\ne0$ this is a quadratic, with $1+\chi(\mathrm{disc}_\kappa)$ roots. A direct expansion gives
$B^2-4N(w_0)N(d)=4\varepsilon(b_0d_2-c_0d_1)^2=4\varepsilon\rho^2$, hence

$$\mathrm{disc}_\kappa=(\kappa B-\rho)^2-4\kappa N(d)(\kappa N(w_0)-a_0)=4\kappa N(d)\,(a_0-a^*_\kappa),\qquad a^*_\kappa=-\frac{4\varepsilon\kappa\rho^2-2B\rho+\rho^2/\kappa}{4N(d)} .$$

Then $a^*_{\kappa_1}-a^*_{\kappa_2}=-\frac{\rho^2}{4N(d)}(\kappa_1-\kappa_2)\bigl(4\varepsilon-\frac1{\kappa_1\kappa_2}\bigr)=0$;
call the common value $a^*$. The line meets the two quadrics in

$$\bigl(1+\chi(\kappa_1)\chi(N(d)(a_0-a^*))\bigr)+\bigl(1+\chi(\kappa_2)\chi(N(d)(a_0-a^*))\bigr)=2$$

points, because $\chi(\kappa_1)\chi(\kappa_2)=\chi(1/(4\varepsilon))=\chi(\varepsilon)=-1$, so
$\chi(\kappa_1)+\chi(\kappa_2)=0$. (If $a_0=a^*$, the line is tangent to both and meets each in one point.)

*Intersection.* $\kappa_1\ne\kappa_2$, since $\kappa_1^2=1/(4\varepsilon)$ is impossible for a non-square
$\varepsilon$. So $\kappa_1N(w)=\kappa_2N(w)$ forces $N(w)=0$, $w=0$, and the common points are $x$ and $e$. $\square$

*Proof of Corollary 4.2.* Theorem 3.2 with $(s,t)=(q-1,q+1)$, $w=\varpi$ of Theorem 4.1 and $\mathcal M=\emptyset$: every
line has $q$ points and gains exactly two clones, every old point is on $q+2$ lines, and every clone is on the $q+2$
lines of its point. The order is $q^3+q^2(q+2)+2q^2=2q^2(q+2)$. $\square$

**Remarks.** Weights are necessary: an integer program shows that $\mathrm{AS}(3)$ has no 1- or 2-ovoid without
repeated points and $\mathrm{AS}(5)$ has no $m$-ovoid for $m=1,\dots,4$ (`research/gq4x`). The structure is regular,
so no choice of clones and shadows on $\mathrm{AS}(q)$ does better at $\Delta=q+2$. Theorem A beats Delorme's
$2q^3+3q^2+3q+6$ by $q^2-3q-6>0$ for $q\ge5$.

**Cells.** $(11,4)$: $1782$ (2013: 1734); $(13,4)$: $3146$ (3064); $(15,4)$: $5070$ (4946). All regular.

**Status.** Paper proof (above; `NOTE.md` §3, `geometry.tex` Theorem 5.6). Computer-checked: the record graphs
1782, 3146, 5070 (three checkers, `NOTE.md` §7); the normalised form above rebuilt from these coordinates for
$q=3,5,7,9$ (regular, diameter 4). Lean-checked for every finite field of odd order: the model of §4.1 has the GQ
counts of order $(q-1,q+1)$, two points on at most one line, and the existence half of the GQ axiom, which is all
that Theorem B uses (`ASq.isGQst`), the weighted 2-ovoid (`ASq.weighted_two_ovoid`), the bound and its regular form
(`ASq.bound`, `ASq.bound_regular`); and the three record graphs (`nb_11_4_v2`, `nb_13_4_v2`, `nb_15_4_v2`).

---

## 5. Proposition C: Singer 2-ovoids of $W(3,q)$, and the $(16,4)$ graph

### 5.1 The cyclic model

Let $q$ be odd, $\mathbb F=\mathrm{GF}(q)\subset K=\mathrm{GF}(q^2)\subset E=\mathrm{GF}(q^4)$, and $g$ a primitive
element of $E$. $E$ is a 4-dimensional $\mathbb F$-space, so $\mathrm{PG}(3,q)=E^*/\mathbb F^*$ (any $\mathbb F$-basis
of $E$ gives homogeneous coordinates); the point $\langle g^i\rangle$ has index $i$ modulo
$(q+1)(q^2+1)$. Write $\bar y=y^{q^2}$ (the involution of $E/K$), $k'=k^q$ for $k\in K$, $\mathrm N(y)=y\bar y\in K$,
$\mathrm{Tr}=\mathrm{Tr}_{K/\mathbb F}$. Let $d=g^{(q^2+1)/2}$; then $\bar d=-d$ and $h=d^2=g^{q^2+1}$ generates $K^*$.
The form

$$b(y,z)=\mathrm{Tr}_{E/\mathbb F}(d\,y\bar z)=\mathrm{Tr}\bigl(d(y\bar z-\bar yz)\bigr)$$

is alternating and non-degenerate; $W(3,q)$ is its symplectic quadrangle. Multiplication by $g^{q+1}$ multiplies $b$
by $g^{(q+1)(q^2+1)}\in\mathbb F^*$, so it is a collineation of $W(3,q)$. Its point orbits are the classes

$$C_a=\{\langle g^i\rangle:\ i\equiv a\pmod{q+1}\},\qquad |C_a|=q^2+1,$$

and $\langle y\rangle\in C_a$ iff $\mathrm N(y)\in h^a\mathbb F^*$ (as $\mathrm N(g^i)=h^i$ and $K^*/\mathbb F^*$ is
cyclic of order $q+1$, generated by $h$). These are Ebert's elliptic quadrics partitioning $\mathrm{PG}(3,q)$ [E85].

The $K$-subspaces $yK$ ($y\in E^*$) are lines of $\mathrm{PG}(3,q)$ (the regular spread), with points
$\langle g^{i+(q^2+1)j}\rangle$, $j=0,\dots,q$. They are totally isotropic: for $k_1,k_2\in K$,
$b(yk_1,yk_2)=\mathrm{Tr}(d\,\mathrm N(y)(k_1k_2-k_1k_2))=0$. So $\Sigma=\{yK\}$ is a spread of $W(3,q)$ with $q^2+1$ lines.

### 5.2 Statement and proof

**Proposition 5.1 (Proposition C).** Let $q$ be odd.

- (a) Every line of $\mathrm{PG}(3,q)$ meets each class $C_a$ in at most two points.
- (b) Every totally isotropic line of $W(3,q)$ meets $C_a\cup C_{q-a}$ in exactly two points.

So the $(q+1)/2$ sets $C_a\cup C_{q-a}$, $0\le a\le(q-1)/2$, are 2-ovoids of $W(3,q)$ partitioning its points (the
pairing $a\leftrightarrow q-a$ has no fixed point, as $2a\equiv-1\pmod{q+1}$ is impossible for $q+1$ even).

*Proof.* Let $L=\langle y,z\rangle_{\mathbb F}$ and $u=sy+tz$ ($s,t\in\mathbb F$). Then
$\mathrm N(u)=A_1s^2+\tau st+A_2t^2$ with $A_1=\mathrm N(y)$, $A_2=\mathrm N(z)$, $\tau=y\bar z+\bar yz$, all in $K$. Put
$\theta=y\bar z-\bar yz$. As $\bar\theta=-\theta$, $\theta/d\in K$; write $\theta=dk_0$, $k_0\in K$. Then

$$\mathcal D:=\tau^2-4A_1A_2=\theta^2=hk_0^2,\qquad b(y,z)=\mathrm{Tr}(hk_0).$$

Fix $\omega\in K^*$ with $\omega'=-\omega$. For $\mu\in K^*$ put $\nu=\omega/\mu$; the kernel of
$k\mapsto\mathrm{Tr}(\nu k)$ is the $\mathbb F$-subspace $\mu\mathbb F$. So $\langle u\rangle$ lies in
$C_\mu:=\{\langle u\rangle:\mathrm N(u)\in\mu\mathbb F^*\}$ iff $(s:t)$ is a zero of the binary form

$$f_\nu(s,t)=\mathrm{Tr}(\nu A_1)s^2+\mathrm{Tr}(\nu\tau)st+\mathrm{Tr}(\nu A_2)t^2 .$$

(a) Suppose $f_\nu\equiv0$. Then $A_1,\tau,A_2\in\mu\mathbb F$. If $\mathcal D\ne0$, then $hk_0^2=\mathcal D\in\mu^2\mathbb F^*$,
so $h\in(K^*)^2\mathbb F^*=(K^*)^2$ (every element of $\mathbb F^*$ is a square in $K$, since $q-1$ divides
$(q^2-1)/2$), but $h$ generates $K^*$, which has even order. If $\mathcal D=0$, then
$\mathrm N(sy+tz)=\mu(\alpha_0s^2+\beta_0st+\gamma_0t^2)$ with $\alpha_0,\beta_0,\gamma_0\in\mathbb F$,
$\beta_0^2=4\alpha_0\gamma_0$ and $\alpha_0\ne0$ (as $A_1\ne0$), which vanishes at $(s:t)=(-\beta_0:2\alpha_0)$:
impossible, since $\mathrm N(u)\ne0$ for $u\ne0$. So $f_\nu\not\equiv0$, and it has $1+\chi(D(\nu))\le2$ projective zeros,
$D(\nu)=\mathrm{Tr}(\nu\tau)^2-4\,\mathrm{Tr}(\nu A_1)\,\mathrm{Tr}(\nu A_2)$.

(b) Expanding with $\mathrm{Tr}(\nu k)=\nu k+\nu'k'$,

$$D(\nu)=\mathrm{Tr}(\nu^2\mathcal D)+\nu\nu'P,\qquad P=2\tau\tau'-4A_1A_2'-4A_1'A_2\in\mathbb F .$$

If $L$ is totally isotropic, $\mathrm{Tr}(hk_0)=0$, so $hk_0\in\omega\mathbb F$ and $\eta:=h\mathcal D=(hk_0)^2\in\omega^2\mathbb F\subseteq\mathbb F$.
Then $\mathrm{Tr}(h^2\nu'^2\mathcal D)=\eta(h\nu'^2+h'\nu^2)=hh'\,\mathrm{Tr}(\nu^2\mathcal D)$, and since
$(h\nu')(h\nu')'=hh'\nu\nu'$,

$$D(h\nu')=\mathrm N_{K/\mathbb F}(h)\,D(\nu).$$

$\mathrm N_{K/\mathbb F}(h)=h^{q+1}$ generates $\mathbb F^*$, so it is a non-square and
$\chi(D(h\nu'))=-\chi(D(\nu))$. The class belonging to $h\nu'$ is $\omega/(h\nu')=-\mu'/h\equiv(h\mu)^{-1}$ modulo
$\mathbb F^*$ (using $\mu^{q+1}\in\mathbb F^*$); in indices $a\mapsto-a-1\equiv q-a\pmod{q+1}$. Scaling $\nu$ by
$\mathbb F^*$ multiplies $D$ by a square. So $L$ meets $C_a\cup C_{q-a}$ in
$(1+\chi(D(\nu)))+(1-\chi(D(\nu)))=2$ points. $\square$

**Remark (literature).** For $q$ odd, $W(3,q)$ has $m$-ovoids for every even $m$ and $(q+1)/2$-ovoids [BLP09], and
[FWX19] states, citing [BLP09], that $W(3,p^e)$ ($p$ odd) has a partition into 2-ovoids. Cossidente, Culbert, Ebert and
Marino [CCEM08] construct $m$-ovoids of $W(3,q)$ with Singer-type stabilisers. We have not been able to check whether
the 2-ovoids $C_a\cup C_{q-a}$ coincide with those; Proposition C is very likely a known object, and we claim only the
short self-contained proof. The proof uses only that $d^2$ is a non-square in $K$: for any $\delta_0$ with
$\bar\delta_0=-\delta_0$, $C_a\cup C_b$ is a 2-ovoid of the form $\mathrm{Tr}_{E/\mathbb F}(\delta_0y\bar z)$ when
$h^{a+b}\delta_0^2\in\mathbb F^*$.

### 5.3 Corollary C1, written in $W(3,q)$

**Corollary 5.2 (Corollary C1).** Let $q$ be odd, $0\le a\le(q-1)/2$, $\mathcal O=C_a\cup C_{q-a}$ and $\Sigma$ the
regular spread $\{yK\}$. Adjoin to $W(3,q)$

- one clone $P'$ of each point $P\in\mathcal O$, incident with the $q+1$ totally isotropic lines on $P$ (the lines
  $\langle P,Z\rangle$ with $b(P,Z)=0$);
- two shadow lines $L',L''$ for each $L\in\Sigma$, each incident with the $q+1$ points of $L$.

The result is bipartite, has diameter 4, maximum degree $q+3$ (old points and old lines have degree $q+3$, clones and
shadow lines $q+1$) and $2(q^2+1)(q+3)$ elements. Joining clone $c_i$ to shadow lines $y_{2i},y_{2i+1}$ (indices modulo
$2(q^2+1)$, any numbering) makes it $(q+3)$-regular with diameter 4. Hence $n_b(q+3,4)\ge2(q^2+1)(q+3)$, with a regular
graph.

*Proof.* $W(3,q)$ is a GQ of order $(q,q)$. By Proposition 5.1(b), $w=\mathbf 1_{\mathcal O}$ is a 2-ovoid
($=\Delta-s-1$ for $\Delta=q+3$), and $\mathcal M=2\Sigma$ is a 2-cover (every point is on exactly one spread line). Apply
Corollary 3.3 with $k=2$. $\square$

This is the point–line dual of the construction in `NOTE.md` §5.4 (clones of an ovoid of $Q(4,q)$ and the dual
2-cover), so it needs no Klein correspondence. (The $(16,4)$ record file was built in the $Q(4,13)$ model; it has the
same order and degrees.) More generally, $j$ copies of the spread and $j/2$ of the 2-ovoid give
$n_b(q+1+j,4)\ge2(q^2+1)(q+1+j)$ for even $j$.

**Corollary 5.3 (Corollary B2: all degrees).** For every prime power $q$ and $\Delta\ge q+1$ there is a $\Delta$-regular
incidence structure of diameter 4 with $2\Delta(q^2+1)$ elements if $q$ is even or $\Delta-q-1$ is even, and
$2\Delta q^2$ elements otherwise. In particular $n_b(\Delta,4)\ge2q^2\Delta$ for every prime power $q\le\Delta-1$.

*Proof.* Corollary 3.3 with $j=\Delta-q-1$. $q$ even: $W(3,q)$ has an ovoid $\mathcal O_0$ and a spread $\Sigma$
[PT, 3.4.1]; take $w=j\mathbf 1_{\mathcal O_0}$, $\mathcal M=j\Sigma$. $q$ odd, $j$ even: $w=(j/2)\mathbf 1_{\mathcal O}$
with $\mathcal O$ a 2-ovoid of Proposition 5.1, $\mathcal M=j\Sigma$. $q$ odd, $j$ odd: then $\Delta\ge q+2$; in
$\mathrm{AS}(q)$ take $(\Delta-q)/2$ copies of the weighted 2-ovoid of Theorem 4.1 and $\Delta-q-2$ copies of the fibre
spread. $\square$

**Cells.** $(16,4)$: $q=13$, $5440=2\cdot170\cdot16$ (2013: 5134), regular. In the range $\Delta\le16$ this is the only
open cell with $\Delta-3$ an odd prime power. Without stand-ins, $5440$ is the most a copy graph on $W(3,13)$ or
$Q(4,13)$ of maximum degree 16 can have (each line takes at most 2 clones and each point at most 2 shadow lines).

**Status.** Paper proof (above; `NOTE.md` §5, `geometry.tex` Proposition 5.9). Computer-checked: exactly the pairs
$\{a,q-a\}$ are 2-ovoids for $q=3,5,7,11,13$ (`research/gq4y/w3_singer.py`) and $q=9,25,27$
(`w3_singer_pp.py`); the 5440 graph (three checkers); the $W(3,q)$ form of Corollary 5.2 for $q=3,5$. Lean-checked,
in exactly this cyclic model and directly in $W(3,q)$ (no Klein correspondence): for every field $E$ of order $q^4$,
$q$ odd, with a chosen primitive element $g$, Proposition C(b) (`SingerC.Setting.propC_subspace`, `SingerC.propC`),
the spread $\{yK\}$ (`SingerC.W3.spread_exists_unique`), Corollary C1 for every even $j\ge2$ (`SingerC.corC1`) and its
regular form (`SingerC.Setting.regular_W3`); such data exist for every odd prime power, but the library constructs
them explicitly only for $q=13$, where it gives the regular 5440 graph (`SingerC.regular5440`). The record file is
also kernel-checked (`nb_16_4_v2`). See Section 9.

---

## 6. Theorem D: the split Cayley hexagon, Hermitian spreads and whiskers (diameter 6)

Throughout §6.1–6.4 $q$ is odd; even $q$ is §6.5.

### 6.1 Coordinates

$Q(6,q)$ is the quadric $X_0X_4+X_1X_5+X_2X_6=X_3^2$ of $\mathrm{PG}(6,q)$, with polar form $B$. The split Cayley
hexagon $H(q)$ has as points all points of $Q(6,q)$, and as lines the lines of $Q(6,q)$ whose Grassmann coordinates
$p_{ij}=x_iy_j-x_jy_i$ satisfy Tits' equations

$$p_{12}=p_{34},\quad p_{54}=p_{32},\quad p_{20}=p_{35},\quad p_{65}=p_{30},\quad p_{01}=p_{36},\quad p_{46}=p_{31}.$$

It is a generalized hexagon of order $(q,q)$ [T59], [VM98, §2.4]: $(q+1)(q^4+q^2+1)$ points and as many lines, any
two elements at distance $\le6$, girth 12. The lines on a point $y$ are the $q+1$ lines on $y$ in a totally singular
plane $\pi_y$. Let $v=\langle e_1,e_6\rangle$ (a line of $H(q)$: no Tits equation involves $p_{16}$). Fix
$c\in\mathbb F$ with $-c$ a non-square. For $z=(\alpha,\beta)\in\mathbb F^2$ let

$$\Pi_z:\ X_0+cX_4+\alpha X_2+\beta X_5=0,\qquad \Pi=\Pi_{(0,0)},$$

and let $S_z$ be the set of lines of $H(q)$ contained in $\Pi_z$; $S=S_{(0,0)}$. Every $\Pi_z$ contains $v$.

**Lemma 6.1.** For every $z\in\mathbb F^2$:

- (a) $\Pi_z\cap Q(6,q)$ is an elliptic quadric $Q^-(5,q)$.
- (b) Every point of $H(q)$ in $\Pi_z$ is on exactly one line of $S_z$. So $|S_z|=q^3+1$, the lines of $S_z$ are
  pairwise opposite, and $v\in S_z$ ($S_z$ is a Hermitian spread [T80]).
- (c) A line of $H(q)$ not in $S_z$ meets $\Pi_z$ in exactly one point.
- (d) The points of $H(q)$ at distance $\le3$ from $v$ are exactly the points of $Q(6,q)$ with $X_2=X_5=0$; among them
  only the points of $v$ lie in $\Pi_z$.
- (e) $S_z\cap S_{z'}=\{v\}$ for $z\ne z'$.

*Proof.* (a) On $\Pi_z$ substitute $X_0=-cX_4-\alpha X_2-\beta X_5$:
$X_0X_4+X_1X_5+X_2X_6-X_3^2=(X_1-\beta X_4)X_5+X_2(X_6-\alpha X_4)-(X_3^2+cX_4^2)$, two hyperbolic planes plus the
anisotropic form $X_3^2+cX_4^2$. So the form on $\Pi_z$ is non-degenerate of Witt index 2.

(b) Let $y\in\Pi_z\cap Q(6,q)$. By (a) $\Pi_z\cap Q(6,q)$ contains no totally singular plane, so
$\pi_y\not\subseteq\Pi_z$ and $\pi_y\cap\Pi_z$ is one line through $y$: the only line of $H(q)$ on $y$ inside
$\Pi_z$. $Q^-(5,q)$ has $(q+1)(q^3+1)$ points, so $|S_z|=q^3+1$. Two lines of $S_z$ are not concurrent (uniqueness). If
two were at distance 4, a line $N$ of $H(q)$ would meet both in distinct points, so $N\subseteq\Pi_z$, $N\in S_z$,
concurrent with them: a contradiction. So they are opposite.

(c) A line not in the hyperplane $\Pi_z$ meets it in one point.

(d) Let $y=ae_1+be_6$ be on $v$ and $yu$ a line of $H(q)$. Then $p_{12}=p_{34}$ gives $au_2=0$, $p_{65}=p_{30}$ gives
$bu_5=0$, and $B(y,u)=0$ gives $au_5+bu_2=0$; so $u_2=u_5=0$. Conversely $Q(6,q)\cap\{X_2=X_5=0\}$ is $X_0X_4=X_3^2$, a
cone with vertex $v$ over a conic, with $(q+1)+(q+1)q^2$ points: exactly the number of points at distance $\le3$ from
$v$ ($q+1$ on $v$, and $q$ more on each of the $q(q+1)$ other lines meeting $v$). If such a point is in $\Pi_z$, then
$X_0=-cX_4$ and $X_3^2+cX_4^2=0$, so $X_0=X_3=X_4=0$ and the point is on $v$.

(e) If $\ell\in S_z\cap S_{z'}$, $\ell\ne v$, then $(\alpha-\alpha')X_2+(\beta-\beta')X_5=0$ on $\ell$, so some point of $\ell$
has $X_2=X_5=0$ and is at distance $\le3$ from $v$ by (d); but $\ell$ and $v$ are opposite by (b), so every point of $\ell$
is at distance 5 from $v$. $\square$

### 6.2 Delorme's levels and whiskers

Let $\mathcal P(v)$ be the points of $v$, $\mathcal L_v$ the $q^2+q$ lines $\ne v$ meeting $v$, and $\mathcal P_\Pi$ the
$(q+1)(q^3+1)$ points of $H(q)$ in $\Pi$. A point is *free* if it is not in $\Pi$ and is at distance 5 from $v$; by
Lemma 6.1(d) there are $(q+1)(q^4+q^2+1)-(q+1)-q^2(q+1)-q^3(q+1)=q^3(q^2-1)$ of them.

**Definition 6.2.** A *whisker set* is a set $W$ of lines of $H(q)$, each opposite $v$ and not in $S$, such that no
free point is on two lines of $W$. It is *exact* if every free point is on exactly one line of $W$.

A line opposite $v$ and not in $S$ meets $\Pi$ in one point, not on $v$ (Lemma 6.1(c),(d)), and its other $q$ points
are free (every point of a line opposite $v$ is at distance 5 from $v$). So $|W|\le q^3(q^2-1)/q=q^2(q^2-1)$, with
equality iff $W$ is exact.

**Theorem 6.3.** Let $W$ be a whisker set and $m\ge2$. Put

$$\mathcal A_2=\{v\},\qquad \mathcal A_1=\{v\}\cup\mathcal P(v)\cup S,\qquad \mathcal A_0=\mathcal A_1\cup\mathcal P_\Pi\cup\mathcal L_v\cup W .$$

Then $\mathcal A$ satisfies (L0), (L1) and (C$_6$). Hence $H(q)^{(m)}_{\mathcal A}$ is bipartite with maximum degree
$q+m$, diameter 6, and

$$2(q+1)(q^4+q^2+1)+(m-1)\bigl(q^4+2q^3+q^2+2q+2+|W|+m(q^3+q+2)+m^2\bigr)$$

elements.

*Proof.* (L1), $i=1$: the elements on $v$ are its points ($\in\mathcal A_1$); a point of $v$ is on one element of
$\mathcal A_2$, a line of $S\setminus\{v\}$ on none. (L1), $i=0$: the elements incident with $\mathcal A_1$ are the
points of $v$, the lines of $\mathcal L_v$ and the points of $\Pi$, all in $\mathcal A_0$; a line of $\mathcal L_v$
meets $v$ in one point and contains no other point of $\mathcal A_1$; a point of $\mathcal P_\Pi\setminus\mathcal P(v)$
is on exactly one line of $S$ (Lemma 6.1(b)) and not on $v$; a whisker has no point on $v$. (L0): a point outside
$\mathcal A_0$ is off $\Pi$. If it is at distance 3 from $v$, it is on exactly one line of $\mathcal L_v$ (two would
close a circuit of length $\le6$) and on no whisker (a whisker through it would be at distance $\le4$ from $v$). If it
is free, it is on no line of $\mathcal L_v$ and on at most one whisker. A line outside $\mathcal A_0$ is not in $\Pi$
(the lines in $\Pi$ are those of $S$), so it meets $\Pi$ in one point, its only point in $\mathcal A_0$. (C$_6$): a line
of $\mathcal L_v$ has no point of $\Pi$ other than its point on $v$ (Lemma 6.1(d)), and a whisker has exactly one point
of $\Pi$, not on $v$. So the components of the substructure on $\mathcal A_0$ are

$$\{v\}\cup\mathcal P(v)\cup\mathcal L_v\qquad\text{and}\qquad \{n\}\cup\mathcal P(n)\cup\{w\in W:w\text{ meets }n\}\quad(n\in S\setminus\{v\}),$$

trees of diameter 4 (the ball of radius 2 about $v$; a line, its points and the whiskers hanging from them). Lemma 1.3
gives (C$_6$), and Theorem 1.2 gives degree $\le q+1+(m-1)$, diameter $\le6$ and the count:
$|\mathcal A_2|=1$, $|\mathcal A_1|=(q^3+1)+(q+1)$, $|\mathcal A_0|=(q^3+1)+(q^2+q)+|W|+(q+1)(q^3+1)$. The diameter is
exactly 6: a free point $p$ (level $-1$) has $q^5$ opposite points, and only $(q+1)(q^3+1)<q^5$ points lie in
$\mathcal A_0$, so some opposite point $p'$ has level $-1$ and $d(p,p')\ge6$ by projection. $\square$

**New vertices: the neighbourhood of every version.** Write $x^w$ for the versions ($a,b,c\in[m]$). Every element of
$H(q)$ appears once in this table.

| element (level) | versions | neighbours of the version | degree |
|---|---|---|---|
| $v$ (2) | $v^{abc}$ | $p^{ab}$ for the $q+1$ points $p$ of $v$ | $q+1$ |
| point $p$ of $v$ (1) | $p^{ab}$ | $v^{ab1},\dots,v^{abm}$; $L^a$ for the $q$ lines $L\in\mathcal L_v$ on $p$ | $q+m$ |
| line $n\in S\setminus\{v\}$ (1) | $n^{ab}$ | $p^a$ for the $q+1$ points $p$ of $n$ | $q+1$ |
| point $p\in\mathcal P_\Pi\setminus\mathcal P(v)$ (0) | $p^a$ | $n^{a1},\dots,n^{am}$ for the line $n\in S$ on $p$; $w^a$ for each whisker $w$ on $p$; every other line on $p$ | $q+m$ |
| line $L\in\mathcal L_v$ (0) | $L^a$ | $p^{a1},\dots,p^{am}$ for $p=L\cap v$; the $q$ other points of $L$ | $q+m$ |
| whisker $w\in W$ (0) | $w^a$ | $p^a$ for $p=w\cap\Pi$; the $q$ free points of $w$ | $q+1$ |
| point $r\notin\Pi$ ($-1$) | $r$ | all $m$ versions of the line of $\mathcal L_v\cup W$ on $r$ (if any); every other line on $r$ | $q+m$, or $q+1$ if $r$ is free and on no whisker |
| line $N\notin\mathcal A_0$ ($-1$) | $N$ | all $m$ versions of its point in $\Pi$ (not on $v$); its $q$ other points | $q+m$ |

An element of level $k$ has $m^{k+1}$ versions. For $m=2$ ($\Delta=q+2$) the number of new elements is
$|\mathcal A_0|+2|\mathcal A_1|+4|\mathcal A_2|$ (Theorem 1.2(c)).

### 6.3 An exact whisker set for every odd $q$

For a point $X$ of $H(q)$ in $\Pi$, not on $v$, put

$$\nu(X)=\frac{X_2X_3-X_4X_5}{cX_2^2+X_5^2}.$$

The denominator vanishes only if $X_2=X_5=0$, i.e. (Lemma 6.1(d)) only on $v$. Let

$$G(a,b)=(c_0a+c_1b)(a^2+cb^2)-b^3,\qquad F(z)=\frac{G(\alpha,\beta)}{\alpha^2+c\beta^2}\quad(z=(\alpha,\beta)\ne0),$$

with $c_0,c_1\in\mathbb F$ chosen so that $G$ has no zero on $\mathbb F^2\setminus\{0\}$.

**Lemma 6.4.** Such $c_0,c_1$ exist for every odd $q$.

*Proof.* $G(a,0)=c_0a^3$, so $c_0\ne0$ is needed. For $b\ne0$ and $t=a/b$, $G(a,b)=b^3\bigl((c_0t+c_1)(t^2+c)-1\bigr)$,
and $t^2+c\ne0$. So $G$ has a zero with $b\ne0$ iff $(c_0,c_1)$ lies on one of the $q$ lines
$c_0t+c_1=1/(t^2+c)$, $t\in\mathbb F$, of the $(c_0,c_1)$-plane; each has $q-1$ points with $c_0\ne0$. The lines for
$t=0$ and $t=1$ meet at $c_0=1/(1+c)-1/c=-1/(c(1+c))\ne0$ ($c\ne-1$ as $-c$ is a non-square). So these lines cover at
most $q(q-1)-1$ of the $q(q-1)$ points with $c_0\ne0$. $\square$

One valid choice for each $q$ in the table ($\mathbb F_9=\mathbb F_3[i]$, $i^2=-1$):

| $q$ | 3 | 5 | 7 | 9 | 11 | 13 |
|---|---|---|---|---|---|---|
| $c$ | 1 | 2 | 1 | $1+i$ | 1 | 2 |
| $(c_0,c_1)$ | (1,2) | (1,0) | (1,0) | $(i,2i)$ | (1,3) | (1,1) |

**Theorem 6.5 (exact whiskers).** Let $q$ be odd, $-c$ a non-square, $c_0,c_1$ as in Lemma 6.4. Then

$$W=\bigl\{\ell\in S_z\setminus\{v\}:\ z\in\mathbb F^2\setminus\{0\},\ \nu(\ell\cap\Pi)=F(z)\bigr\}$$

is an exact whisker set: every free point lies on exactly one line of $W$, and $|W|=q^2(q^2-1)$.

(Here $\ell\cap\Pi$ is one point not on $v$: $\ell\subseteq\Pi_z$, $\ell\ne v$, so $\ell\notin S$ by Lemma 6.1(e) and $\ell$ is
opposite $v$ by Lemma 6.1(b).) The proof uses a complex structure on each $\Pi_z$. Write a point of $\Pi_z$ as
$x=(x_1,\dots,x_6)$, meaning $(X_0,\dots,X_6)=(-cx_4-\alpha x_2-\beta x_5,x_1,\dots,x_6)$; on $\Pi_z$ the quadratic
form is $Q_z(x)=x_1x_5+x_2x_6-x_3^2-cx_4^2-\alpha x_2x_4-\beta x_4x_5$, with polar form $B_z$. Put
$\mathrm{num}(y)=y_2y_3-y_4y_5$ and $\mathrm{den}(y)=cy_2^2+y_5^2$, and define the linear map

$$J_zx=\bigl(-\beta x_3+\alpha x_4-x_6,\ x_5,\ -cx_4-\beta x_5,\ x_3+\beta x_2,\ -cx_2,\ cx_1+\alpha\beta x_2+\alpha x_3+c\beta x_4+\beta^2x_5\bigr);$$

for $z=0$, $J_0x=(-x_6,x_5,-cx_4,x_3,-cx_2,cx_1)$.

**Lemma 6.6 (complex structure).** For every $z$:

- (a) $J_z^2=-c$, $Q_z(J_zx)=cQ_z(x)$ and $B_z(x,J_zx)=0$.
- (b) The six differences $p_{12}-p_{34}$, $p_{54}-p_{32}$, $p_{20}-p_{35}$, $p_{65}-p_{30}$, $p_{01}-p_{36}$,
  $p_{46}-p_{31}$ of the Grassmann coordinates of $x\wedge J_zx$ equal $Q_z(x)$ times $1,0,0,-c,\alpha,-\beta$.
- (c) For every point $x$ of $Q(6,q)\cap\Pi_z$, the line $\langle x,J_zx\rangle$ is the line of $S_z$ through $x$.
- (d) $\mathrm{num}(sx+tJ_0x)=(s^2+ct^2)\,\mathrm{num}(x)$ and $\mathrm{den}(sx+tJ_0x)=(s^2+ct^2)\,\mathrm{den}(x)$.
  So $\nu$ is constant on every line of $S\setminus\{v\}$.

*Proof.* (a), (b) and (d) are polynomial identities with integer coefficients, checked by direct expansion (for
instance, for $z=0$: $Q_0(J_0x)=cx_2x_6+cx_1x_5-c^2x_4^2-cx_3^2=cQ_0(x)$, and $p_{12}=x_1x_5+x_2x_6$,
$p_{34}=x_3^2+cx_4^2$, so $p_{12}-p_{34}=Q_0(x)$; in (d), $\mathrm{num}(J_0x)=c\,\mathrm{num}(x)$,
$\mathrm{den}(J_0x)=c\,\mathrm{den}(x)$, and the polar forms $x_2y_3+x_3y_2-x_4y_5-x_5y_4$ and $2cx_2y_2+2x_5y_5$
vanish at $y=J_0x$). We re-checked all of them with sympy for this note (`polish/jz.py`). (c) $J_z$ has no eigenvector ($-c$ is a
non-square), so $x,J_zx$ span a line; if $Q_z(x)=0$, then by (a) the whole line is singular and by (b) its Grassmann
coordinates satisfy Tits' equations, so it is a line of $H(q)$ in $\Pi_z$ through $x$, the one of Lemma 6.1(b). (d)
By (c), a line $n\in S\setminus\{v\}$ is $\{sx+tJ_0x\}$ for any of its points $x$, and $s^2+ct^2\ne0$. $\square$

Let $p$ be a free point. By Lemma 6.1(d), $(p_2,p_5)\ne(0,0)$; as $p\notin\Pi$ we normalise $p_0+cp_4=1$. Then
$p\in\Pi_z$ iff $z$ lies on the affine line

$$A_p=\{(\alpha,\beta):\ \alpha p_2+\beta p_5=-1\}\subseteq\mathbb F^2\setminus\{0\},$$

which has $q$ points and direction $(p_5,-p_2)$. For $z\in A_p$ let $\ell_p(z)$ be the line of $S_z$ on $p$ and
$X(z)=\ell_p(z)\cap\Pi$.

**Lemma 6.7 (key identity).** For $z=(\alpha,\beta)\in A_p$,

$$\Phi_p(z):=\nu(X(z))+\frac{\beta^3}{\alpha^2+c\beta^2}=\frac{p_2p_3-p_4p_5+\beta p_2^2}{cp_2^2+p_5^2}.$$

So $\Phi_p$ is affine on $A_p$, with increment $-p_2^3/(cp_2^2+p_5^2)$ along $(p_5,-p_2)$.

*Proof.* Put $\Theta=cp_2^2+p_5^2\ne0$ and $\gamma=-\alpha p_5+c\beta p_2$. On $\Pi_z$ the function
$\lambda(y)=y_0+cy_4$ equals $-\alpha y_2-\beta y_5$, and $\Pi=\{\lambda=0\}$. We have $\lambda(p)=1$ and
$\lambda(J_zp)=-\alpha p_5+c\beta p_2=\gamma$. By Lemma 6.6(c), $\ell_p(z)=\langle p,J_zp\rangle$, so
$X(z)=\gamma p-J_zp$, with

$$X_2=\gamma p_2-p_5,\quad X_3=\gamma p_3+cp_4+\beta p_5,\quad X_4=\gamma p_4-p_3-\beta p_2,\quad X_5=\gamma p_5+cp_2 .$$

Expanding, $\mathrm{den}(X)=(\gamma^2+c)\Theta$ and
$\mathrm{num}(X)=(\gamma^2+c)(p_2p_3-p_4p_5)+\beta(2\gamma p_2p_5+cp_2^2-p_5^2)$. Solving $\alpha p_2+\beta p_5=-1$,
$-\alpha p_5+c\beta p_2=\gamma$ (determinant $\Theta$) gives $\alpha=-(cp_2+\gamma p_5)/\Theta$,
$\beta=(\gamma p_2-p_5)/\Theta$, hence $\alpha^2+c\beta^2=(\gamma^2+c)/\Theta$ ($\ne0$) and
$\beta^3/(\alpha^2+c\beta^2)=\beta(\gamma p_2-p_5)^2/((\gamma^2+c)\Theta)$. The two $\beta$-terms add up to
$\beta\bigl(2\gamma p_2p_5+cp_2^2-p_5^2+(\gamma p_2-p_5)^2\bigr)/((\gamma^2+c)\Theta)=\beta p_2^2/\Theta$. Along
$(p_5,-p_2)$, $\beta$ changes by $-p_2$. $\square$

*Proof of Theorem 6.5.* Let $p$ be free. The lines of $\bigcup_{z\ne0}S_z\setminus\{v\}$ on $p$ are exactly the $q$
lines $\ell_p(z)$, $z\in A_p$, and they are distinct (a common line would lie in $S_z\cap S_{z'}=\{v\}$); since
$S_z\cap S_{z'}=\{v\}$, each line of $W$ belongs to a single $S_z$. As
$F(z)=c_0\alpha+c_1\beta-\beta^3/(\alpha^2+c\beta^2)$, we have $\ell_p(z)\in W$ iff $\Phi_p(z)-(c_0\alpha+c_1\beta)=0$.
The left side is affine on $A_p$ with increment

$$-\frac{p_2^3}{\Theta}-(c_0p_5-c_1p_2)=-\frac{G(p_5,-p_2)}{\Theta}\ne0$$

along $(p_5,-p_2)$, so it vanishes at exactly one of the $q$ points of $A_p$: $p$ is on exactly one line of $W$. The
lines of $W$ are opposite $v$ and not in $S$. Counting incidences between free points and $W$ gives
$|W|=q^3(q^2-1)/q$. $\square$

### 6.4 Theorem D

**Corollary 6.8 (Theorem D).** For every odd prime power $q$ and every $m\ge2$, the structure of Theorem 6.3 with
the exact whisker set of Theorem 6.5 is bipartite, has maximum degree $q+m$ and diameter 6, and

$$n_b(q+m,6)\ge2(q+1)(q^4+q^2+1)+(m-1)\bigl(2q^4+2q^3+2q+2+m(q^3+q+2)+m^2\bigr).$$

In particular $n_b(q+2,6)\ge2(q+1)(q^4+q^2+1)+2q^4+4q^3+4q+10$ and
$n_b(q+3,6)\ge2(q+1)(q^4+q^2+1)+4q^4+10q^3+10q+34$.

With $W$ exact, every element outside $\mathcal A_0$ is incident with exactly one element of $\mathcal A_0$; by the
counting bound for doublings of a generalized $n$-gon of order $(q,q)$ with $N$ points,
$q|\mathcal A_0|+2k\le2N$ ($k$ the number of components of $\mathcal A_0$; `geometry.tex` Prop. 3.6), the
single-level part is as large as possible (here $k=q^3+1$).

**Remark 6.9 (Delorme's construction: the 2013 values).** $W=\emptyset$ is Delorme's doubling of $H(q)$ along a
Hermitian spread [D85a, D85b]. At $m=2$ it has $2(q+1)(q^4+q^2+1)+q^4+4q^3+q^2+4q+10$ elements: $8992$, $142464$,
$374452$, $842048$ at $q=5,9,11,13$; at $q=13$, $m=3$, it gives $884062$. These are the 2013 table values at
$\Delta=7,11,13,15,16$. The exact whiskers add $(m-1)q^2(q^2-1)$.

**Cells.** $m=2$: $(7,6)$ $9592$ (2013: 8992), $(11,6)$ $148944$ (142464), $(13,6)$ $388972$ (374452), $(15,6)$
$870440$ (842048). $m=3$, $q=13$: $(16,6)$ $940846$ (884062). These graphs are not regular (Section 7).

**Status.** Paper proof (above; `geometry.tex` §6). Computer-checked: the graphs for $q=5,7,9,11,13$ (and $q=13$,
$m=3$) were built and their exact diameter computed by all-pairs BFS; exactness of $W$ checked on all free points for
$q=3,5,7$; the identities of Lemmas 6.6–6.7 re-checked symbolically. Lean-checked for every finite field of odd
characteristic: $H(q)$ in these coordinates is a generalized hexagon in the graph sense
(`Hexagon.genPolygonGraph_hexagon`), Theorem 6.5 for every admissible $(c,c_0,c_1)$
(`HexagonD.wset_whiskers`, `exists_unique_wline`; `theorem4` packages it with the count $|W|=q^4-q^2$), Theorem 6.3 for any whisker set
(`HexagonD.whiskers_bound_hexagon`), Corollary 6.8 (`HexagonD.theoremD`, `theoremD_two`), Lemma 6.4
(`exists_goodCubic`), Lemma 6.7 (`HexagonD.Identity.key_identity`) and Lemma 6.6(d) (`nu_eq_of_mem_sline`); for even
$q\ge4$ (`HexagonEven.theorem4_even`, `theoremD_even`) and $q=2$, $m=2$ (`HexagonEven.theoremD_q2`); and the 9592
graph itself (`nb_7_6`). See Section 9.

### 6.5 Even $q$

Let $q=2^e$, $\mathrm{Tr}$ the absolute trace of $\mathbb F$, and fix $\delta\in\mathbb F$ with $\mathrm{Tr}(\delta)=1$, so
that $t^2+t+\delta$ is irreducible and $a^2+ab+\delta b^2$ is anisotropic. $Q(6,q)$ is now
$X_0X_4+X_1X_5+X_2X_6+X_3^2=0$, with nucleus $e_3$ (every hyperplane $X_0+cX_4+\dots=0$ of §6.1 contains it), and
$H(q)$ is given by the same Tits equations. Instead put

$$\Pi_z:\ X_3=X_0+\delta X_4+\alpha X_2+\beta X_5\qquad(z=(\alpha,\beta)\in\mathbb F^2),\qquad \Pi=\Pi_{(0,0)},$$

$S_z$ the lines of $H(q)$ in $\Pi_z$, and $v=\langle e_1,e_6\rangle\subseteq\Pi_z$ as before.

**Lemma 6.10.** Lemma 6.1 holds verbatim for even $q$ with these $\Pi_z$.

*Proof.* (a) On $\Pi_z$, $X_0X_4+X_1X_5+X_2X_6+X_3^2=(X_0^2+X_0X_4+\delta^2X_4^2)+(X_1+\beta^2X_5)X_5+X_2(X_6+\alpha^2X_2)$.
The first term is anisotropic ($\mathrm{Tr}(\delta^2)=\mathrm{Tr}(\delta)=1$) and the polar form is non-degenerate on
$\Pi_z$ (which misses $e_3$), so $\Pi_z\cap Q(6,q)$ is an elliptic quadric $Q^-(5,q)$. (b), (c), (e) are proved as in
Lemma 6.1. (d) The same three equations give $u_2=u_5=0$ (only signs change); on $X_2=X_5=0$ the quadric is the cone
$X_0X_4=X_3^2$, and in $\Pi_z$ this becomes $X_0^2+X_0X_4+\delta^2X_4^2=0$, so $X_0=X_4=X_3=0$, a point of $v$. $\square$

So Theorem 6.3 (doubling with whiskers) holds for even $q$ without change; there are $q^3(q^2-1)$ free points and an
exact whisker set has $q^2(q^2-1)$ lines. For $X\in\Pi$ not on $v$ put

$$\nu(X)=\frac{X_2X_3+X_2X_4+X_4X_5}{\delta X_2^2+X_2X_5+X_5^2},\qquad G(a,b)=(c_0a+c_1b)(a^2+ab+\delta b^2)+b^3,\qquad F(z)=\frac{G(\alpha,\beta)}{\alpha^2+\alpha\beta+\delta\beta^2}.$$

The denominator of $\nu$ is anisotropic and vanishes only on $v$.

**Lemma 6.11.** There are $c_0,c_1\in\mathbb F$ with $G$ zero-free on $\mathbb F^2\setminus\{0\}$ iff $q\ge4$.

*Proof.* $G(a,0)=c_0a^3$ needs $c_0\ne0$. For $b\ne0$, $t=a/b$: $G=0$ iff $c_0t+c_1=r(t):=1/(t^2+t+\delta)$, a line in the
$(c_0,c_1)$-plane with $q-1$ points having $c_0\ne0$. If $q\ge4$ take $\omega\notin\{0,1\}$; then $r(\omega)\ne r(0)$
(as $\omega^2+\omega\ne0$), so the lines for $t=0,\omega$ meet at $c_0=(r(0)+r(\omega))/\omega\ne0$, and the $q$ lines
cover fewer than $q(q-1)$ points with $c_0\ne0$. If $q=2$ then $\delta=1$, $r(0)=r(1)=1$, and the lines $c_1=1$,
$c_0+c_1=1$ contain both points with $c_0=1$. $\square$

On $\Pi_z$ use coordinates $x=(x_0,x_1,x_2,x_4,x_5,x_6)$, with $X_3=x_0+\delta x_4+\alpha x_2+\beta x_5$, and

$$J_zx=\bigl((\delta+1)x_0+\delta\alpha x_2+\delta^2x_4+(\alpha+\delta\beta)x_5,\ \beta x_0+x_1+\alpha\beta x_2+(\alpha+\delta\beta)x_4+\beta^2x_5+x_6,\ x_2+x_5,$$
$$\qquad x_0+(\alpha+\beta)x_2+\delta x_4+\beta x_5,\ \delta x_2,\ (\alpha+\beta)x_0+\delta x_1+\alpha^2x_2+\delta\alpha x_4+\alpha\beta x_5\bigr).$$

**Lemma 6.12.** With $Q$ the quadratic form and $B$ its polar form: (a) $J_z^2+J_z+\delta=0$, $Q(J_zx)=\delta Q(x)$,
$B(x,J_zx)=Q(x)$; (b) the six Tits differences of $x\wedge J_zx$ are $Q(x)$ times $1,0,0,\delta,\alpha,\beta$; (c) for
every point $x$ of $Q(6,q)\cap\Pi_z$, $\langle x,J_zx\rangle$ is the line of $S_z$ on $x$; (d) with
$\mathrm{num}=X_2X_3+X_2X_4+X_4X_5$, $\mathrm{den}=\delta X_2^2+X_2X_5+X_5^2$ on $\Pi$,
$\mathrm{num}(sx+tJ_0x)=(s^2+st+\delta t^2)\mathrm{num}(x)$ and likewise for $\mathrm{den}$; so $\nu$ is constant on
every line of $S\setminus\{v\}$.

*Proof.* (a), (b), (d) are polynomial identities over $\mathbb F_2[\delta,\alpha,\beta,x]$, checked by expansion
(`research/evenq/proof_J.py`, re-run for this note). (c) $J_z$ has no eigenvector since $t^2+t+\delta$ is irreducible;
if $Q(x)=0$ then $Q(sx+tJ_zx)=(s^2+st+\delta t^2)Q(x)=0$ by (a), and by (b) the line satisfies Tits' equations, so it is
the line of Lemma 6.10(b). In (d), $s^2+st+\delta t^2\ne0$ for $(s,t)\ne0$. $\square$

Let $p$ be free, normalised by $p_0+p_3+\delta p_4=1$. With $\lambda(y)=y_0+y_3+\delta y_4$ we have
$\Pi=\{\lambda=0\}$ and $\lambda=\alpha y_2+\beta y_5$ on $\Pi_z$, so $p\in\Pi_z$ iff $z$ lies on the affine line
$A_p:\ \alpha p_2+\beta p_5=1$ (direction $(p_5,p_2)$). For $z\in A_p$ let $\ell_p(z)$ be the line of $S_z$ on $p$ and
$X(z)=\ell_p(z)\cap\Pi$.

**Lemma 6.13 (key identity, characteristic 2).** For $z=(\alpha,\beta)\in A_p$,
$$\Phi_p(z):=\nu(X(z))+\frac{\beta^3}{\alpha^2+\alpha\beta+\delta\beta^2}=\frac{p_2p_3+p_2p_4+p_4p_5+\beta p_2^2}{\delta p_2^2+p_2p_5+p_5^2},$$
which is affine on $A_p$ with increment $p_2^3/\Theta$ along $(p_5,p_2)$, $\Theta=\delta p_2^2+p_2p_5+p_5^2\ne0$.

*Proof.* $\lambda(p)=1$ and $\gamma:=\lambda(J_zp)=\alpha(p_2+p_5)+\delta\beta p_2$. By Lemma 6.12(c),
$X(z)=\gamma p+J_zp$ (then $\lambda(X)=2\gamma=0$); $X_2=(\gamma+1)p_2+p_5$, $X_5=\delta p_2+\gamma p_5$. Expanding,
$\mathrm{den}(X)=(\gamma^2+\gamma+\delta)\Theta$ and
$\mathrm{num}(X)=(\gamma^2+\gamma+\delta)(p_2p_3+p_2p_4+p_4p_5)+\beta\bigl((\gamma+\delta+1)p_2^2+p_5^2\bigr)$, with
$\gamma^2+\gamma+\delta\ne0$. Solving $\alpha p_2+\beta p_5=1$, $\alpha(p_2+p_5)+\delta\beta p_2=\gamma$ (determinant
$\Theta$): $\alpha=(\delta p_2+\gamma p_5)/\Theta$, $\beta=((\gamma+1)p_2+p_5)/\Theta$, so
$\alpha^2+\alpha\beta+\delta\beta^2=(\gamma^2+\gamma+\delta)/\Theta$ and
$\beta^3/(\alpha^2+\alpha\beta+\delta\beta^2)=\beta((\gamma+1)p_2+p_5)^2/((\gamma^2+\gamma+\delta)\Theta)$. The
$\beta$-terms add to $\beta\bigl((\gamma+\delta+1)+(\gamma+1)^2\bigr)p_2^2/((\gamma^2+\gamma+\delta)\Theta)=\beta p_2^2/\Theta$.
Along $(p_5,p_2)$, $\beta$ changes by $p_2$. (These expansions are re-checked in `research/evenq/proof_J2.py`.) $\square$

**Theorem 6.14 (exact whiskers, even $q\ge4$).** With $c_0,c_1$ as in Lemma 6.11,
$W=\{\ell\in S_z\setminus\{v\}:z\ne0,\ \nu(\ell\cap\Pi)=F(z)\}$ is an exact whisker set.

*Proof.* As for Theorem 6.5: the lines of $\bigcup_{z\ne0}S_z\setminus\{v\}$ on a free $p$ are the $q$ distinct lines
$\ell_p(z)$, $z\in A_p$, and $\ell_p(z)\in W$ iff $\Phi_p(z)+c_0\alpha+c_1\beta=0$, since
$F(z)=c_0\alpha+c_1\beta+\beta^3/(\alpha^2+\alpha\beta+\delta\beta^2)$. The left side is affine on $A_p$ with
increment $p_2^3/\Theta+c_0p_5+c_1p_2=G(p_5,p_2)/\Theta\ne0$, so it vanishes at exactly one point. $\square$

**Corollary 6.15.** Corollary 6.8 and Theorem 7.3 hold for every even $q\ge4$. For $q=2$ the formula gives no whisker
set (Lemma 6.11), but an exact whisker set of $12=q^2(q^2-1)$ lines exists: it was found by an integer program
(`research/evenq/whiskers_raw_q2.json`) and its exactness is kernel-checked (`HexagonEven.q2_exact`); so Corollary 6.8
and Theorem 7.3 with $m=2$ hold for $q=2$ as well (208 and 192 vertices). None of this changes a table cell with
$\Delta\le16$: for $q=2,4,8$ the degree $q+2$ is a Moore degree, and at $\Delta=q+3$ the odd prime power $q+1$ gives
more.


---

## 7. Theorem R: regular graphs of diameter 6

The structure of Corollary 6.8 has equally many points and lines in $\mathcal A_0$ (exact whiskers force this), but
$\mathcal A_1$ has $q^3+1$ lines and only $q+1$ points, and $\mathcal A_2$ is a line. So it has
$(m-1)m(q^3-q+m)$ more lines than points. We delete repeated lines and then add anti-flags.

**Lemma 7.1 (repeated lines).** In $H(q)^{(m)}_{\mathcal A}$, for $n\in S\setminus\{v\}$ and $a\in[m]$ the $m$ lines
$n^{a1},\dots,n^{am}$ all have the point set $\{p^a:p\in n\}$; for $a,b\in[m]$ the lines $v^{ab1},\dots,v^{abm}$ all
have the point set $\{p^{ab}:p\in v\}$ (table of §6.2). So there are $mq^3+m^2$ classes of $m$ repeated lines.

**Lemma 7.2 (completion).** Let a finite incidence structure have maximum degree $\le\Delta$, every element of degree
$\ge\Delta-r$, and $\sum_{\text{points}}(\Delta-\deg)=\sum_{\text{lines}}(\Delta-\deg)=:T$. If $T>2r\Delta$, there is a
set $J$ of anti-flags such that adding $J$ makes it $\Delta$-regular.

*Proof.* Choose a multiset $J$ of point–line pairs in which each element $x$ occurs $\Delta-\deg x$ times (possible as
the sums agree). Call an entry bad if it is a flag or a repeat of another entry, and take $J$ with fewest bad entries.
If $(p,L)$ is bad: $L$ is joined (in $\mathrm I\cup J$, with multiplicity) to $\Delta$ points, each in $\le r$ entries of
$J$; likewise $p$. So at most $2r\Delta<T$ entries $(p',L')$ have $p'$ joined to $L$ or $L'$ joined to $p$, and some
entry $(p',L')$ has neither (it is not $(p,L)$ itself). Replacing $(p,L),(p',L')$ by $(p,L'),(p',L)$ removes a bad
entry and creates none. So the minimum is 0. $\square$

**Theorem 7.3 (Theorem R).** For every odd prime power $q$ and $m\ge2$ (even $q$: Corollary 6.15) there is a $(q+m)$-regular incidence structure
of diameter at most 6 with

$$2(q+1)\bigl(q^4+q^2+1+(m-1)(q^3+m+1)\bigr)$$

elements: $2(q+1)(q^4+q^3+q^2+4)$ for $m=2$ and $2(q+1)(q^4+2q^3+q^2+9)$ for $m=3$. For the five table instances the
order exceeds $M_b(q+m,5)$, so the diameter is exactly 6.

*Proof.* Start from Corollary 6.8. Fix a set $R$ of $q$ lines of $S\setminus\{v\}$, and delete the lines
$v^{abc}$ with $c\ge2$ ($(m-1)m^2$ lines) and $n^{ab}$ with $b\ge2$ for $n\notin R$ ($(m-1)m(q^3-q)$ lines): in total
$(m-1)m(q^3-q+m)$, the excess, so points and lines are now equal in number. Each class of Lemma 7.1 keeps at least one
line, so by Lemma 0.2(b) no distance between remaining elements increases. After the deletion the degrees are:
$p^{ab}$ ($p\in v$) $q+1$; $p^a$ on a line $n\notin R$ of $S$: $q+1$; $p^a$ on $n\in R$: $q+m$; $v^{ab1}$, $n^{a1}$
($n\notin R$), $n^{ab}$ ($n\in R$) and $w^a$ ($w\in W$): $q+1$; all others as in §6.2 ($q+m$). So every deficit is at
most $r=m-1$, and $T$ is at least the deficit of the $m|W|$ whisker versions:
$T\ge(m-1)mq^2(q^2-1)>2(m-1)(q+m)$. Lemma 7.2 completes the structure; added flags join a point to a line, so the
graph stays bipartite, and they do not increase distances. The number of points is
$(q+1)(q^4+q^2+1)+(m-1)\bigl((q+1)(q^3+1)+m(q+1)\bigr)$. $\square$

**Neighbourhoods.** Every neighbourhood is that of the table in §6.2, minus the deleted lines listed above, plus the
$(m-1)$ (for each deficient element, exactly its deficit) completing anti-flags. The completing anti-flags are not
given by a formula: Lemma 7.2 proves they exist, and `research/p4/regular/regularize.py` finds them by a seeded swap
procedure (it uses its own deletion choice, not necessarily $R$ above). Neither the maximum degree nor the diameter
depends on that choice.

**Cells (regular graphs).** $(7,6)$ $9348$, $(11,6)$ $147500$, $(13,6)$ $386328$, $(15,6)$ $866068$, $(16,6)$ $927724$
($q=13$, $m=3$). Each beats the 2013 value of its cell (8992, 142464, 374452, 842048, 884062), and Delorme's graphs
behind those values are not regular (their point side is larger).

**Status.** Paper proof (above; `geometry.tex` Theorem 6.13; `research/p4/regular/REPORT.md`). Computer-checked:
all five regular graphs are exactly regular with equal sides and diameter exactly 6 (independent all-pairs checks).
Lean-checked: `HexagonD.theoremR`, `theoremR_two` (every finite field of odd characteristic); `HexagonEven.theoremR`,
`theoremR_two` (even $q\ge4$; their docstrings wrongly say "odd $q$", the statements are for characteristic 2);
`HexagonEven.theoremR_q2` ($q=2$, $m=2$, 192 vertices). See Section 9.

---

## 8. The Haar lemma (diameter 5)

This one is group-theoretic, not geometric; it is included because it gives the $(7,5)$ and $(9,5)$ cells.

**Definition 8.1.** For a finite group $G$ and $S\subseteq G$, the *Haar graph* $H(G,S)$ has vertex set
$G\times\{A,B\}$ and edges $(g,A)\sim(sg,B)$ for $g\in G$, $s\in S$. So

$$N(g,A)=\{(sg,B):s\in S\},\qquad N(h,B)=\{(s^{-1}h,A):s\in S\},$$

it is bipartite and $|S|$-regular on $2|G|$ vertices, and right multiplication by $G$ acts on it as automorphisms.

**Lemma 8.2 (Haar lemma).** If $S\ne\emptyset$ and every element of $G$ is a product $a^{-1}bc^{-1}d$ and also a
product $ab^{-1}cd^{-1}$ with $a,b,c,d\in S$, then $H(G,S)$ has diameter at most 5.

*Proof.* Two steps from $(g,A)$ reach $(t g,B)$ and then $(s^{-1}tg,A)$, $s,t\in S$: they multiply on the left by
$s^{-1}t$. So the $A$-vertices within distance 4 of $(g,A)$ include $\{(a^{-1}bc^{-1}d\,g,A)\}=G\times\{A\}$. Likewise
two steps from $(h,B)$ reach $(s^{-1}h,A)$ and $(ts^{-1}h,B)$, so the $B$-vertices within distance 4 of $(h,B)$ are all
of $G\times\{B\}$. For $(g,A)$ and $(h,B)$: one step to $(sg,B)$ ($s\in S$), then at most 4. $\square$

More generally (Lean `haar_ediam_le_odd`, `haar_ediam_le_even`): if every element is a product of at most $n$ factors
$s^{-1}t$ and of at most $n$ factors $ab^{-1}$, the diameter is $\le2n+1$; if every element is $s\,y$ with $s\in S$ and
$y$ a product of at most $n$ factors $s^{-1}t$, the diameter is $\le2n+2$.

**The records.** The covering conditions are finite checks; for both graphs the Lean files contain, for every group
element, a quadruple from $S$ that represents it (`lean/BipartiteDD/Haar/Cert1152.lean`, `Cert2662.lean`), checked by
the kernel.

- $(7,5)$, 1152 vertices: $G=S_4\times\mathbb Z_{24}$ (order 576), product $(f,x)(h,y)=(f\circ h,x+y)$, and
  $$S=\{(\mathrm{id},0),\ ((0\,1)(2\,3),23),\ ((0\,3\,2),0),\ ((0\,2),18),\ ((0\,1\,2\,3),18),\ ((1\,2\,3),17),\ ((1\,2),3)\},$$
  permutations of $\{0,1,2,3\}$ in cycle notation (Lean lists them in one-line form $[f(0),f(1),f(2),f(3)]$).
- $(9,5)$, 2662 vertices: $G$ the Heisenberg group mod 11, $(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab')$ (the matrix
  $\left(\begin{smallmatrix}1&a&c\\0&1&b\\0&0&1\end{smallmatrix}\right)$ over $\mathbb Z_{11}$), and
  $$S=\{(0,0,0),(8,6,10),(7,9,3),(10,1,8),(4,4,5),(5,5,8),(6,5,4),(1,0,9),(6,10,8)\}.$$
- $(8,5)$, 1764 vertices: $G=\mathrm{AGL}(1,7)\times\mathbb Z_{21}$ as $(x,y,z)\in\mathbb Z_7\times\mathbb Z_6\times\mathbb Z_{21}$,
  $(x,y,z)(x',y',z')=(x+3^yx',y+y',z+z')$, $S=\{(0,0,0),(0,4,5),(6,3,18),(6,5,6),(2,4,1),(2,2,16),(4,5,12),(2,3,15)\}$.
  (This cell's current record, 2048, comes from a different lift construction not covered here.)

**Cells.** $(7,5)$: $1152$ (2013: 1134). $(9,5)$: $2662$ (2013: 2496). $(8,5)$: $1764$ (2013: 1710; superseded).
All regular.

**Status.** Paper proof (above). Computer-checked: the record files pass the lab's checkers, and for this note all
three graphs were rebuilt from $(G,S)$ exactly as printed above (order 1152, 2662, 1764; diameter 5, from the
eccentricities of $(e,A)$ and $(e,B)$, which suffice because right multiplication is transitive on each side).
Lean-checked: the lemma for every group
(`Haar.haar_ediam_le_five`, `haar_isBipartiteDegDiam`) and the record graphs (`nb_7_5_v2` for 1152, `nb_9_5_v6` for
2662, `nb_8_5_v2` for 1764).

---

## 9. Exactly what is Lean-checked

All theorems below are in `lean/BipartiteDD` (Lean 4.34.1, Mathlib commit `d13f23b7`). For each, `#print axioms`
(files `lean/Axioms.out.txt`, `lean/RegularAxioms.out.txt`, `lean/BipartiteDD/*/Axioms.out.txt`) lists only `propext`,
`Classical.choice`, `Quot.sound` (a few helper lemmas list a subset). `grep` finds no `sorry`, `admit`, `axiom` or
`native_decide` in any `.lean` file, and no `implemented_by`, `extern`, `unsafe` or `ofReduceBool`; finite checks use
`decide` / `decide +kernel`, which the kernel checks.

**The graph predicate.** `IsBipartiteDegDiam G d D` means: $G$ is 2-colourable, every vertex has at most $d$
neighbours, and the diameter (`ediam`, which is $\infty$ for a disconnected graph) is at most $D$.
`IsBipartiteRegDiam G Δ D` is the same with every vertex of degree exactly $\Delta$. Every record statement has the
form "there is a graph on `Fin N` with this property", so the vertex count is exactly $N$; diameters are upper bounds.

**Two conventions to know.**
1. `GQst P L s t` (the generalized-quadrangle hypothesis) records: lines have $s+1$ points, points are on $t+1$ lines,
   two points are on at most one line, and for an anti-flag $(p,L)$ *some* point of $L$ is collinear with $p$ (the
   existence half of the GQ axiom). Theorems that *assume* `GQst` are therefore slightly stronger than their paper
   statements; theorems that *conclude* `GQst` (`ASq.isGQst`, `SingerC.W3.isGQst`) prove less than "is a GQ", but
   exactly what Theorem B needs.
2. $\mathrm{AS}(q)$, $W(3,q)$ and $H(q)$ are each given by the coordinate model used in this note; Lean does not prove
   that the model is isomorphic to the classical object (we cite [P71], [PT], [T59], [VM98] for that). The generalized
   polygon predicate `GenPolygonGraph G n` is: 2-colourable, girth $2n$, diameter $n$, every vertex has two distinct
   neighbours.

**Section 1 (doubling, hat lemma).** `Doubling.delorme_levelled`, `isBipartiteDegDiam_levelled`,
`card_levelled_levels`: Theorem 1.2(a)–(c) for any finite graph that is bipartite of maximum degree $\le\Delta$ and
diameter $\le D$, with (L0), (L1), (C$_D$) as hypotheses, giving maximum degree $\le\Delta+m-1$, diameter $\le D$ and
the exact count. `Doubling.condC_of_forestDiam` (any graph with all degrees $\ge2$) and
`GenPolygonGraph.condC_iff_forestDiam` (both directions of the hat lemma); `delorme_levelled_polygon` (Corollary 1.4,
"if"). Theorem 1.2(d) is not formalised.

**Section 2 (fourth hat).** `Plus2.plus2_regular`: for every finite projective plane (Mathlib's `ProjectivePlane`, not
necessarily Desarguesian) with a frame (a line $\ell$, a point $A\notin\ell$, five distinct points of $\ell$), there is
a $(q+2)$-regular bipartite graph on $2(q^2+q+6)$ vertices of diameter $\le3$. `plus2_regular_of_order`: the same for
every finite projective plane of order $q\ge4$. (`plus2`, `plus2_of_order`: the non-regular version.) Records:
`nb_11_3` (192), `nb_13_3` (276), `nb_15_3` (376), explicit graphs. A variant that keeps every incidence of the plane,
for $q\ge3$, is `Plus2Zero.zero_isBipartiteDegDiam` (not described in this note).

**Section 3 (Theorem B).** For every finite `GQst P L s t` and multiplicities $w:P\to\mathbb N$, $m:L\to\mathbb N$
with line sums of $w$ at most $a$ and point sums of $m$ at most $b$: `GQST.gqst` (all stand-ins original) gives a
bipartite graph on $|P|+|L|+\sum w+\sum m$ vertices with maximum degree $\le\max(s+1+a,t+1+b)$ and diameter $\le4$;
`GQST.standin_gqst` is the same with arbitrary stand-ins and "each stand-in serves at most $b$ line copies";
`GQST.regular_copy_graph`, `regular_copy_graph_fin`: with exact sums ($\Delta-s-1$ and $\Delta-t-1$) the graph can be
made $\Delta$-regular with diameter $\le4$ (Corollary 3.3). Record: `nb_7_4` (the 359 file
`records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json`).

**Section 4 (Theorem A).** For every finite field $\mathbb F$ of odd characteristic, with $q=|\mathbb F|$:
`ASq.isGQst` (the coordinate model of §4.1 is `GQst` of order $(q-1,q+1)$), `ASq.weighted_two_ovoid` (Theorem 4.1's
line count, for $\varepsilon$ a non-square and $c_1c_2=1/(4\varepsilon)$), `ASq.bound` and `ASq.bound_regular` (a
$(q+2)$-regular bipartite graph on $2q^2(q+2)$ vertices of diameter $\le4$). Records: `nb_11_4_v2` (1782),
`nb_13_4_v2` (3146), `nb_15_4_v2` (5070).

**Section 5 (Proposition C, Corollary C1).** For every field $E$ of order $q^4$, $q=p^e$ odd, with a chosen element
$g$ of order $q^4-1$ (a `SingerC.Setting`): `SingerC.Setting.propC_subspace` and `SingerC.propC` (every totally
isotropic line of $W(3,q)$, in the model of §5.1, has exactly 2 points in $C_a\cup C_{q-a}$, for every $a\le q$),
`SingerC.W3.isGQst`, `SingerC.W3.spread_exists_unique` (the lines $yK$ form a spread), `SingerC.corC1` (for every even
$j\ge2$, a bipartite graph on $2(q^2+1)(q+1+j)$ vertices with maximum degree $\le q+1+j$ and diameter $\le4$, built in
$W(3,q)$ itself) and `SingerC.Setting.regular_W3` (the regular graph of Corollary 5.2). Such fields and elements exist
for every odd prime power, but the library constructs one only for $q=13$ (`setting13`), giving
`SingerC.regular5440` (a 16-regular bipartite graph on 5440 vertices of diameter $\le4$). Record: `nb_16_4_v2` (the
5440 file).

**Section 6 (Theorem D).** For every finite field of odd characteristic: `Hexagon.genPolygonGraph_hexagon` ($H(q)$ in
the coordinates of §6.1 is a generalized hexagon in the graph sense); `HexagonD.wset_whiskers` and `exists_unique_wline` (for every $c$ with
$-c$ a non-square and every $(c_0,c_1)$ with $G$ zero-free, $W$ of Theorem 6.5 is a whisker set and every free point is
on exactly one of its lines), `HexagonD.theorem4` (for some such $c,c_0,c_1$, also $|W|+q^2=q^4$); `HexagonD.whiskers_bound_hexagon` (Theorem 6.3 for any whisker set);
`HexagonD.theoremD`, `theoremD_two` (Corollary 6.8 for every $m\ge1$, resp. $m=2$, with the exact vertex counts);
`HexagonD.exists_goodCubic` (Lemma 6.4); `HexagonD.Identity.key_identity` (Lemma 6.7, over any field) and
`nu_eq_of_mem_sline` (Lemma 6.6(d)). Even $q$: `HexagonEven.genPolygonGraph_hexagon_even` (any finite field),
`theorem4_even`, `theoremD_even` ($q\ge4$); `theoremD_q2` and `q2_exact` ($q=2$, $m=2$, the 12 explicit whiskers).
Record: `nb_7_6` (the 9592 file).

**Section 7 (Theorem R).** `HexagonD.theoremR`, `theoremR_two` (odd characteristic, $m\ge2$, resp. $m=2$): a
$(q+m)$-regular bipartite graph of diameter $\le6$ on $2(q+1)(q^4+q^2+1+(m-1)(q^3+m+1))$ vertices.
`HexagonEven.theoremR`, `theoremR_two` (characteristic 2, $q\ge4$), `theoremR_q2` ($q=2$, $m=2$, 192 vertices).

**Section 8 (Haar).** For every group $G$ and finite nonempty $S$: `Haar.haar_ediam_le_five`,
`haar_isBipartiteDegDiam` (Lemma 8.2), `haar_ediam_le_odd`, `haar_ediam_le_even`. Records `nb_7_5_v2` (1152),
`nb_9_5_v6` (2662), `nb_8_5_v2` (1764).

**Not formalised.** Theorem 1.2(d); the identification of the coordinate models with the classical $\mathrm{AS}(q)$,
$W(3,q)$, $H(q)$; the converse of the Haar lemma; that the 359 graph decomposes as in §3 (Lean checks the graph, not
its description); a general existence lemma for `SingerC.Setting`; Theorem R's completion is proved in Lean but, as on
paper, non-constructively.

**Build provenance.** A full `lake build` of the library passed on 2026-10-20 (`lean/CHECK.txt`, 9115 jobs; heavy
record modules rebuilt one at a time). Several modules were added after that date (`HexagonD/Regular`,
`HexagonEven`, `Haar/GraphD`, on which the current `Haar.Main` depends). **For this note (2026-10-25) the 23 modules
behind every general theorem cited above were rebuilt from a fresh clone** (Lean 4.34.1, Mathlib `d13f23b7`, one
`lake build <module>` at a time): all exit 0, including `HexagonD.Regular.Final`, `HexagonEven.ThmD`, `HexagonEven.Q2`,
`HexagonEven.Reg.Final`, `Haar.Main` and the three Haar records, `GQST.StandinMain` and `SingerC.Regular5440`. A
`#print axioms` run on the 48 theorem names cited in this section gives `[propext, Classical.choice, Quot.sound]` for
every one (`research/theorems/polish/lean/PolishAxioms.lean`, `.out`, and `BUILD.txt` with the per-module log;
`ExtraAxioms.lean` adds `exists_unique_wline` and `wset_whiskers`, same result), and
the grep for `sorry`/`admit`/`axiom`/`native_decide` in `lean/BipartiteDD/**.lean` finds nothing. The explicit record
graphs were rebuilt the same day: `Records.lean`, `Records9592.lean` and all 91 modules they import (one at a time;
four first attempts were killed for lack of memory and passed on retry), and `#print axioms` on `nb_11_3`, `nb_13_3`,
`nb_15_3`, `nb_7_4`, `nb_11_4_v2`, `nb_13_4_v2`, `nb_15_4_v2`, `nb_16_4_v2`, `nb_7_6` gives the same three axioms
(`polish/lean/RecordAxioms.lean`, `.out`).

---

## References

- [AS69] R. W. Ahrens, G. Szekeres, On a combinatorial generalization of 27 lines associated with a cubic surface,
  J. Austral. Math. Soc. 10 (1969) 485–492.
- [ADFL21] G. Araujo-Pardo, C. Dalfó, M. A. Fiol, N. López, Bipartite biregular Moore graphs, arXiv:2103.11443
  (Section 4 doubles every line of a GQ to get biregular graphs; our clones and shadow lines are a weighted,
  partial version of that idea).
- [AL20] G. Araujo-Pardo, N. López, On new record graphs close to bipartite Moore graphs, Graphs Combin. 38 (2022),
  no. 4, Paper 110; arXiv:2005.02427 (three hats, $n_b(q+2,3)\ge2(q^2+q+5)$; Problem 4 asks for diameters 4 and 6).
- [BGS06] S. Ball, P. Govaerts, L. Storme, On ovoids of parabolic quadrics, Des. Codes Cryptogr. 38 (2006) 131–145.
- [BLP09] J. Bamberg, M. Law, T. Penttila, Tight sets and $m$-ovoids of generalised quadrangles, Combinatorica 29
  (2009) 1–17.
- [CCEM08] A. Cossidente, C. Culbert, G. L. Ebert, G. Marino, On $m$-ovoids of $W_3(q)$, Finite Fields Appl. 14 (2008)
  76–84.
- [CDPS22] M. Ceria, J. De Beule, F. Pavese, V. Smaldore, On large partial ovoids of symplectic and Hermitian polar
  spaces, J. Combin. Des. 31 (2023) 5–22.
- [D85a] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302.
- [D85b] C. Delorme, Large bipartite graphs with given degree and diameter, J. Graph Theory 9 (1985) 325–334.
  (Which of [D85a], [D85b] contains the doubling with levels and the $D=4,6$ constructions is still to be checked.)
- [DF84] C. Delorme, G. Farhi, Large graphs with given degree and diameter, Part I, IEEE Trans. Comput. C-33 (1984)
  857–860.
- [E85] G. L. Ebert, Partitioning projective geometries into caps, Canad. J. Math. 37 (1985) 1163–1175.
- [FWX19] T. Feng, Y. Wang, Q. Xiang, On $m$-ovoids of symplectic polar spaces, arXiv:1909.07954.
- [MS13] M. Miller, J. Širáň, Moore graphs and beyond: a survey of the degree/diameter problem, Electron. J. Combin.
  Dynamic Survey DS14v2 (2013), Table 4 (the "2013" column).
- [P71] S. E. Payne, Nonisomorphic generalized quadrangles, J. Algebra 18 (1971) 201–212.
- [PT] S. E. Payne, J. A. Thas, Finite Generalized Quadrangles, 2nd ed., EMS, 2009.
- [T59] J. Tits, Sur la trialité et certains groupes qui s'en déduisent, Publ. Math. IHÉS 2 (1959) 13–60.
- [T80] J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A 29 (1980) 87–93.
- [Tal91] G. Tallini, Blocking sets with respect to planes in PG(3,q) and maximal spreads of a nonsingular quadric in
  PG(4,q), Mitt. Math. Sem. Giessen 201 (1991) 141–147 (Proceedings of the First International Conference on Blocking
  Sets, Giessen 1989; pages as cited by Klein–Metsch, Innov. Incidence Geom.).
- [VM98] H. Van Maldeghem, Generalized Polygons, Birkhäuser, 1998.
- [CW] CombinatoricsWiki, The degree diameter problem for bipartite graphs (values read 2026-10-10).

---

## Appendix A. The $(7,4)$ example in coordinates

$Q(4,5)$: the quadric $X_0^2+X_1X_2+X_3X_4=0$ of $\mathrm{PG}(4,5)$, with its $156$ points and $156$ lines (points are
written with first non-zero coordinate 1). Ovoid $\mathcal O=Q(4,5)\cap\{X_4=2X_3\}$ ($-2$ is a non-square mod 5), an
elliptic quadric with 26 points. The structure:

- the incidence graph of $Q(4,5)$ (312 vertices, all of degree 6);
- one clone $o'$ of each $o\in\mathcal O$, joined to the 6 lines on $o$ (26 vertices; every line gains exactly one
  clone, as $\mathcal O$ is an ovoid);
- 21 shadow lines, one for each line below, joined to its six points, except that a starred point is replaced by its
  clone (the stand-in).

```
 1  (0:0:0:0:1) (0:1:0:0:0)  (0:1:0:0:1) (0:1:0:0:2)  (0:1:0:0:3)  (0:1:0:0:4)
 2  (0:0:0:1:0) (0:1:0:0:0)* (0:1:0:1:0) (0:1:0:2:0)  (0:1:0:3:0)  (0:1:0:4:0)
 3  (0:0:1:0:0) (1:0:0:2:2)  (1:0:1:2:2) (1:0:2:2:2)  (1:0:3:2:2)  (1:0:4:2:2)
 4  (0:0:1:0:1) (1:2:0:3:3)  (1:2:1:3:4) (1:2:2:3:0)  (1:2:3:3:1)  (1:2:4:3:2)
 5  (0:0:1:0:2) (1:1:0:2:2)  (1:1:1:2:4) (1:1:2:2:1)  (1:1:3:2:3)  (1:1:4:2:0)
 6  (0:0:1:0:4) (1:3:0:3:3)  (1:3:1:3:2) (1:3:2:3:1)  (1:3:3:3:0)  (1:3:4:3:4)
 7  (0:0:1:1:0) (1:4:0:4:1)  (1:4:1:0:1) (1:4:2:1:1)  (1:4:3:2:1)  (1:4:4:3:1)
 8  (0:0:1:2:0) (1:4:0:3:3)  (1:4:1:0:3) (1:4:2:2:3)  (1:4:3:4:3)  (1:4:4:1:3)
 9  (0:0:1:3:0) (1:2:0:4:1)  (1:2:1:2:1) (1:2:2:0:1)  (1:2:3:3:1)* (1:2:4:1:1)
10  (0:0:1:4:0) (1:4:0:1:4)  (1:4:1:0:4) (1:4:2:4:4)  (1:4:3:3:4)  (1:4:4:2:4)
11  (0:1:1:1:4) (1:0:3:4:1)  (1:1:4:0:0) (1:2:0:1:4)  (1:3:1:2:3)  (1:4:2:3:2)
12  (0:1:1:2:2) (1:0:0:1:4)  (1:1:1:3:1) (1:2:2:0:3)  (1:3:3:2:0)  (1:4:4:4:2)
13  (0:1:1:3:3) (1:0:2:3:3)  (1:1:3:1:1) (1:2:4:4:4)  (1:3:0:2:2)  (1:4:1:0:0)
14  (0:1:1:4:1) (1:0:2:4:1)  (1:1:3:3:2) (1:2:4:2:3)  (1:3:0:1:4)  (1:4:1:0:0)*
15  (0:1:2:1:3) (1:0:3:3:3)  (1:1:0:4:1) (1:2:2:0:4)  (1:3:4:1:2)  (1:4:1:2:0)
16  (0:1:2:2:4) (1:0:3:1:4)  (1:1:0:3:3) (1:2:2:0:2)  (1:3:4:2:1)  (1:4:1:4:0)
17  (0:1:3:2:1) (1:0:1:3:3)  (1:1:4:0:4) (1:2:2:2:0)  (1:3:0:4:1)  (1:4:3:1:2)
18  (0:1:3:3:4) (1:0:4:1:4)  (1:1:2:4:3) (1:2:0:2:2)  (1:3:3:0:1)  (1:4:1:3:0)
19  (0:1:4:1:1) (1:0:4:3:3)  (1:1:3:4:4) (1:2:2:0:0)  (1:3:1:1:1)  (1:4:0:2:2)
20  (0:1:4:2:3) (1:0:0:3:3)  (1:1:4:0:1) (1:2:3:2:4)  (1:3:2:4:2)  (1:4:1:1:0)
21  (0:1:4:4:4) (1:0:0:4:1)  (1:1:4:3:0) (1:2:3:2:4)* (1:3:2:1:3)  (1:4:1:0:2)
```

*What to check by hand* (Theorem 3.2(b) with $s=t=5$, $\Delta=7$): each listed line lies on the quadric; the 21 lines
are pairwise disjoint except at the four ovoid points $(0:1:0:0:0)$, $(1:2:3:3:1)$, $(1:4:1:0:0)$, $(1:2:3:2:4)$, each
on exactly two of them (lines 1 and 2, 4 and 9, 13 and 14, 20 and 21), and on the second of the two the point is
replaced by its clone. So every old point and every clone serves at most one shadow line. Degrees: old lines
$6+1=7$; old points $6$ or $7$; clones $6$ or $7$; shadow lines $6$. Order $156+156+26+21=359$; diameter 4 by
Theorem 3.2(a). The list was produced by `research/theorems/polish/q4_359.py` (HiGHS proves 21 optimal for this
family), which also rebuilds the graph and checks maximum degree 7 and diameter 4. Lean checks the record file of the
same order (`nb_7_4`), which has the same shape (Section 3), not this particular list.
