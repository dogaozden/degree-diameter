<!-- Generated from CONICS.tex by make_md.py; the figures are in CONICS.pdf. -->

# What plays the role of a conic: the lab's constructions and ovals, ovoids and polarities

*Degree–diameter lab, 29 October 2026. Markdown copy of `CONICS.tex`; the PDF has the figures.*

*Abstract.* A sequel to `SYNTHETIC.md` (branch `claude/synthetic-incidence-geometry-s4m08f`), written for Gabriela Araujo-Pardo and Ignacio López, who asked what happens with conics in generalized polygons. We first say what a conic is combinatorially (an oval, and the set of absolute points of a polarity) and what plays these two roles in generalized quadrangles and hexagons. Then we look at each construction of the lab through these objects. In a projective plane of odd order the answer is sharp: if the frame of the three-hat or four-hat construction is placed relative to a conic (the special point is the pole of the special line, two marked points are the points of contact of the tangents from it, and the other two marked points are conjugate), the polarity of the conic extends to a polarity of the whole structure (Theorem 1.4). This explains the links and the rotation, gives an explicit regular completion (the polarity itself), and folds the structure into a graph of diameter $2$ with $q^2+q+6$ vertices and maximum degree $q+2$. A conic-adapted choice does not give a fifth hat: every such frame is infeasible in the hat model for $q\le13$, and no self-polar five-hat extension exists at $q=5$. In quadrangles and hexagons the conic-like objects (ovoids, partial ovoids, spreads, elliptic quadric sections) are already the ingredients of Theorems A–D and of the diameter-$7$ freed sets; we restate how, give Theorem A as a statement about pairs of conics, and record what the polarity picture gives there. No lab value is improved. Every statement is labelled \[new\], \[restatement\] or \[standard\], and \[proof\], \[computer\] or \[heuristic\].

# 0. Conventions and the dictionary

We use the conventions of `SYNTHETIC.md` §0: an incidence structure has points, lines and a symmetric incidence $\mathrel{\mathrm{I}}$; its incidence graph has the elements as vertices and the flags as edges; distances and the diameter are taken there. For the hat constructions we use the frame and the six rules (R1)–(R6) of `SYNTHETIC.md`, Definition 1.1, with the same names: anti-flag $(A,\ell)$, marked points $X_s$ on $\ell$ ($s\in S$), lines $\lambda_s=AX_s$, a distinguished label $a$, $T=S\setminus\{a\}$, links $\pi$ and rotation $\rho$ (permutations of $T$), new points $Q,H_s$ and new lines $M,K_s$.

## 0.1 What a conic is, combinatorially

In $\mathrm{PG}(2,q)$ a *conic* $\mathcal{C}$ is a set of $q+1$ points, no three collinear (an *oval*); for $q$ odd every oval is a conic (Segre). For $q$ odd a conic is also the set of absolute points ($p\mathrel{\mathrm{I}}p^\perp$) of an *orthogonal polarity* $\perp$: an incidence-preserving involution exchanging points and lines. Both descriptions have analogues in generalized polygons, and they are different objects there:

<div class="center">

|                                          | projective plane                                                                  | generalized quadrangle                                                                                             | generalized hexagon                                                                                                                                                             |
|:-----------------------------------------|:----------------------------------------------------------------------------------|:-------------------------------------------------------------------------------------------------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| “no two too close” (arc / partial ovoid) | arc: no $3$ collinear; oval: $q+1$ points ($q+2$, hyperoval, $q$ even)            | partial ovoid: pairwise non-collinear; ovoid: $st+1$ points, one on every line                                     | distance-$2$ (partial) ovoid: non-collinear ($q^4+q^2+1$ points, one on every line; known only for $q=2,3,4$); distance-$3$ (partial) ovoid: pairwise opposite ($q^3+1$ points) |
| absolute points of a polarity            | conic ($q$ odd); a line ($q$ even, pseudo-polarity); Hermitian curve ($q$ square) | Suzuki–Tits ovoid of $W(q)$, $q=2^{2e+1}$ (the only case with a polarity); absolute lines form a spread            | Ree–Tits ovoid of $H(q)$, $q=3^{2e+1}$ (the only case with a polarity); absolute lines form a spread                                                                            |
| dual object                              | dual conic (tangent lines)                                                        | spread                                                                                                             | spread (Hermitian spread, every $q$)                                                                                                                                            |
| quadric sections                         | conic $=$ plane section of a quadric                                              | $Q(4,q)$: elliptic sections $Q^-(3,q)$ are ovoids; plane sections are conics ($q+1$ pairwise non-collinear points) | $Q(6,q)$: elliptic sections $Q^-(3,q)$ are partial ovoids ($q^2+1$); the lines in an elliptic hyperplane $Q^-(5,q)$ form a spread (Hermitian spread)                            |

</div>

\[standard\] \[VM98, PT, Th81, BGS06\]. The lab’s constructions use the first and third rows throughout (Sections 2 and 3). The second row, the polarity, is what explains the hats (Section 1).

## 0.2 Polarities fold incidence structures

A *polarity* of an incidence structure $\mathcal{S}$ is a bijection $\theta$ from points to lines and lines to points with $\theta^2=\mathrm{id}$ and $p\mathrel{\mathrm{I}}L\iff\theta(L)\mathrel{\mathrm{I}}\theta(p)$. A point $p$ is *absolute* if $p\mathrel{\mathrm{I}}\theta(p)$. The *polarity graph* $G_\theta$ has the points of $\mathcal{S}$ as vertices, $p\sim r$ iff $p\ne r$ and $p\mathrel{\mathrm{I}}\theta(r)$ (symmetric because $\theta$ is a polarity). For $\mathrm{PG}(2,q)$ with an orthogonal polarity this is the Erdős–Rényi graph.

**Lemma 0.1 (Folding).** \[standard; proof\] Let $\mathcal{S}$ have a polarity $\theta$, all degrees at most $\Delta$ and diameter $D\ge2$. Then $G_\theta$ has maximum degree at most $\Delta$ and diameter at most $D-1$, and $|V(G_\theta)|$ is half the number of elements of $\mathcal{S}$.

*Proof.* The degree of $p$ in $G_\theta$ is the number of lines through $p$, minus one if $p$ is absolute. Map each element $x$ of a path in the incidence graph to $x$ if it is a point and to $\theta(x)$ if it is a line. Consecutive elements $u\mathrel{\mathrm{I}}L$ go to $u$ and $\theta(L)$, which are equal or adjacent in $G_\theta$ (as $u\mathrel{\mathrm{I}}\theta(\theta(L))$). So a path of length $m$ from $p$ to an element $y$ gives a walk of length at most $m$ from $p$ to $y$ or $\theta(y)$. For points $p\ne r$, $d(p,r)$ is even and $d(p,\theta(r))$ is odd, both at most $D$; the smaller of the two is at most $D-1$. $\square$

So a self-polar bipartite graph of diameter $D$ gives a graph of diameter $D-1$ with half the vertices. In this note it is used in two ways: as a description of what the conic does to the hats (§1.3), and to compare with the tables of the general degree–diameter problem (where it gives nothing new; §§1.3, 2.4, 3.2).

# 1. Projective planes: the hats relative to a conic

## 1.1 The conic frame

Let $q$ be odd, $\mathcal{C}$ a conic of $\Pi=\mathrm{PG}(2,q)$ and $\perp$ its polarity. A point off $\mathcal{C}$ is *external* (on two tangents) or *internal* (on none). We use the following standard facts \[standard\].

**Proposition 1.1 (Conjugation on a polar line).** Let $A\notin\mathcal{C}$ and $\ell=A^\perp$. For a point $X$ of $\ell$, the polar line $X^\perp$ passes through $A$; write $X^\tau=X^\perp\cap\ell$. Then $\tau$ is an involution of the points of $\ell$ and $X^\perp=AX^\tau$. Its fixed points are the points of $\ell\cap\mathcal{C}$: two points $Z,Z'$ if $A$ is external (then $AZ$, $AZ'$ are the two tangents from $A$, touching $\mathcal{C}$ at $Z$ and $Z'$), none if $A$ is internal. If $A$ is external, $X^\tau$ is the harmonic conjugate of $X$ with respect to $Z,Z'$; $X$ and $X^\tau$ are *conjugate* points.

So there are two matchings between the points of $\ell$ and the lines through $A$: the frame matching $X\mapsto AX$, which rule (R1) uses, and the polar matching $X\mapsto X^\perp=AX^\tau$. They differ by $\tau$. The marked points are now chosen as follows.

**Definition 1.2 (Conic frame).** Let $A$ be external, $\ell=A^\perp$, $\ell\cap\mathcal{C}=\{Z,Z'\}$, and $X\in\ell\setminus\mathcal{C}$. *Three hats:* $(X_a,X_0,X_1)=(Z,X,X^\tau)$. *Four hats:* $(X_a,X_c,X_0,X_1)=(Z,Z',X,X^\tau)$. In words: $A$ is the pole of $\ell$; the marked points are the two points of contact of the tangents from $A$ (only one of them for the three hats) and a pair of points of $\ell$ that separates them harmonically. The lines $\lambda_a=AZ$ and $\lambda_c=AZ'$ are the tangents from $A$, and $\lambda_0=(X^\tau)^\perp$, $\lambda_1=X^\perp$.

For every odd $q\ge3$ such frames exist ($\ell\setminus\mathcal{C}$ has $q-1\ge2$ points). The cross-ratio $(X_a,X_c;X_0,X_1)$ of a four-hat conic frame is $-1$; conversely every four-hat frame with $(X_a,X_c;X_0,X_1)=-1$ is a conic frame for each conic of the pencil of conics tangent to $AX_a$ at $X_a$ and to $AX_c$ at $X_c$. \[standard\]

## 1.2 The polarity extends

Let $\tau$ also denote the permutation of labels with $X_{\tau(s)}=X_s^\tau$; in a conic frame $\tau$ swaps $0$ and $1$ and fixes $a$ (and $c$). The next lemma is stated for any polarity $\theta$ of a projective plane with $\theta(A)=\ell$; then $\tau$, defined by $X^\tau=\theta(X)\cap\ell$, is again an involution of $\ell$ whose fixed points are the absolute points of $\ell$.

**Lemma 1.3.** \[new; proof\] Let $\Pi$ be a projective plane with a polarity $\theta$, $A$ a non-absolute point, $\ell=\theta(A)$, and let the marked set $\{X_s\}$ be $\tau$-invariant. Suppose $$\tau(a)=a,\qquad \tau\pi\tau=\pi^{-1},\qquad \tau\rho\tau=\rho^{-1}\quad\text{(on $T$)}.$$ Then $\hat\theta$, equal to $\theta$ on $\Pi$ and with $H_s\leftrightarrow K_{\tau(s)}$, $Q\leftrightarrow M$, is a polarity of the structure $\mathcal{S}=\mathcal{S}(\Pi;A,\ell,(X_s),\pi,\rho)$ of `SYNTHETIC.md`, Definition 1.1.

*Proof.* $\hat\theta$ is an involution exchanging points and lines; we show that it maps each flag $(p,L)$ of $\mathcal{S}$ to a flag $(\hat\theta(L),\hat\theta(p))$. Note $\theta(X_s)=AX_{\tau(s)}=\lambda_{\tau(s)}$ and hence $\theta(\lambda_s)=X_{\tau(s)}$.

(R1) $\theta$ maps flags of $\Pi$ to flags of $\Pi$. The deleted flags $(X_s,\lambda_s)$ go to $(\theta(\lambda_s),\theta(X_s))=(X_{\tau(s)},\lambda_{\tau(s)})$, again deleted. An added flag $(X_t,\lambda_{\rho(t)})$ goes to $(X_{\tau\rho(t)},\lambda_{\tau(t)})$; with $u=\tau\rho(t)$ we have $\rho(u)=\rho\tau\rho(t)=\tau(t)$, because $\tau\rho\tau=\rho^{-1}$ gives $\rho\tau\rho=\tau$. So it is the added flag $(X_u,\lambda_{\rho(u)})$.

(R2)$\leftrightarrow$(R3) If $N\mathrel{\mathrm{I}}X_s$, $N\ne\ell$, then $\theta(N)$ is a point of $\theta(X_s)=\lambda_{\tau(s)}$ other than $\theta(\ell)=A$, so $(\theta(N),K_{\tau(s)})$ is a flag by (R3). The converse is the same computation.

(R4)$\leftrightarrow$(R5) A point $p\in\ell$ goes to the line $\theta(p)=Ap^\tau$ through $A$. If $p$ is unmarked, so is $p^\tau$, and $\theta(p)\in\Lambda^*$; $\theta(X_a)=\lambda_a\in\Lambda^*$; and $\theta(X_t)=\lambda_{\tau(t)}$ with $\tau(t)\in T$. So $\theta$ maps $\ell^*$ onto $\Lambda^*$, and $(p,M)\mapsto(Q,\theta(p))$ preserves (R4)/(R5). $(H_s,M)\mapsto(Q,K_{\tau(s)})$.

(R6) $(A,K_a)\mapsto(H_a,\ell)$. A link $(H_t,K_{\pi(t)})$ goes to $(H_{\tau\pi(t)},K_{\tau(t)})$, and with $u=\tau\pi(t)$, $\pi(u)=\pi\tau\pi(t)=\tau(t)$; so it is the link of $u$. $\square$

**Theorem 1.4 (Self-polar hats).** \[new; proof and computer\] Let $q$ be odd. In a conic frame (Definition 1.2) the polarity of the conic, extended by $$H_a\leftrightarrow K_a,\quad H_c\leftrightarrow K_c,\quad H_0\leftrightarrow K_1,\quad H_1\leftrightarrow K_0,
\quad Q\leftrightarrow M,$$ is a polarity of the three-hat structure of \[AL20\] and of the four-hat structure.

*Proof.* Lemma 1.3 with $\tau=(0\ 1)$. Three hats: $\pi=(0\ 1)$ commutes with $\tau$ and is an involution, $\rho=\mathrm{id}$. Four hats: $\pi=\rho=\sigma=(0\ c\ 1)$ and $\tau\sigma\tau=(1\ c\ 0)=\sigma^{-1}$. $\square$

*Computer.* `conics/polar_frames.py` checks the theorem for every conic frame (every external $A$, every choice of $Z$, $X$) for $q=3,5,7$, and for random frames at $q=9,11,13$; four independent squad programs (`squads/conics-r1/c1`–`c4`) re-derived it from the rules for $q=3,\dots,13$ and over $\mathrm{GF}(9)$, $\mathrm{GF}(25)$ (163 instances), and showed for $q=5,7$ that, with $\theta$ and $\tau$ as above, *exactly* the conic frames are self-polar (2,496 labelled frames tried). The same lemma gives self-polar three hats for $q$ even: the absolute points of a pseudo-polarity form a line $m$, so $\ell=\theta(A)$ has exactly one absolute point $X_a$ and $\tau=(0\ 1)$ as before, unless $\ell=m$, in which case every point of $\ell$ is absolute, $\tau$ is the identity and any three marked points will do. For $q$ square a unitary polarity has $\sqrt q+1$ absolute points on $\ell$, which gives self-polar three and four hats. Checked for $q=4,8,16$ (pseudo) and $q=4,9,16$ (unitary), and independently by squad card `c8` on every non-absolute $A$ at $q=4,8$ (pseudo) and $q=4,9$ (unitary): 6,830 instances, all self-polar with the right $\tau$ (the card’s two “failures” are the two $\ell=m$ cases, where its brief wrongly assumed $\tau\ne\mathrm{id}$).

**Remark 1.5 (Why the conic frame is forced).** \[proof\] For the four hats, a permutation $\tau$ of $S$ as in Lemma 1.3 must fix $a$, preserve $T$ and invert the $3$-cycle $\sigma$; so it is a transposition on $T$ and fixes exactly two labels, $a$ and one $t\in T$. Hence $X_a$ and $X_t$ are absolute points of $\ell$: for an orthogonal polarity, the two points of contact of the tangents from $A$. For the three hats, $\tau$ fixes $a$ and either swaps $0,1$ or fixes them; the second needs three absolute points on $\ell$, impossible for a conic. So among frames with $A$ the pole of $\ell$, the conic frames are the only ones to which the lemma applies; the squad check above confirms that no other labelled frame is self-polar with this $\theta$.

## 1.3 What the gadget is, in polar terms

Under the polarity every line is $\theta$ of a point, so every incidence $p\mathrel{\mathrm{I}}L$ is a symmetric relation “$p$ is conjugate to $\theta(L)$” between two points. Reading Table 3 of `SYNTHETIC.md` this way:

**Proposition 1.6.** \[new; proof\] In a four-hat conic frame:

(1) the four deleted flags $(X_s,\lambda_s)=(X_s,X_{\tau(s)}^\perp)$ are exactly the conjugate pairs among the marked points: $Z$ and $Z'$ with themselves (they are absolute), and $\{X_0,X_1\}$;

(2) the three rotation flags $(X_0,\lambda_c),(X_c,\lambda_1),(X_1,\lambda_0)$ make $X_0$ and $Z'$ conjugate (two flags, $X_0\mathrel{\mathrm{I}}Z'^\perp$ and $Z'\mathrel{\mathrm{I}}X_0^\perp$) and $X_1$ absolute ($X_1\mathrel{\mathrm{I}}X_1^\perp$);

(3) the links are the conjugacies $H_0$–$H_c$ (two flags) and $H_1$ absolute, and $A\mathrel{\mathrm{I}}K_a$, $H_a\mathrel{\mathrm{I}}\ell$ are the two flags of the conjugacy $A$–$H_a$;

(4) $Q$ is conjugate to every $H_s$, to $Z$ and to the unmarked points of $\ell$; $H_s$ is conjugate to the $q$ points of $\lambda_{\tau(s)}$ other than $A$.

So the surgery on the old points replaces the conjugacy relation on the marked set $\{Z,Z',X_0,X_1\}$ (two absolute points and one conjugate pair) by another one (one conjugate pair, $X_0$–$Z'$, and one absolute point, $X_1$), and the links do the same on the hats.

*Proof.* (a) $\lambda_s=AX_s=\theta(X_{\tau(s)})$. (b) $\lambda_c=AZ'=Z'^\perp$, $\lambda_1=X_0^\perp$, $\lambda_0=X_1^\perp$. (c) $K_c=\hat\theta(H_c)$, $K_1=\hat\theta(H_0)$, $K_0=\hat\theta(H_1)$, $K_a=\hat\theta(H_a)$, $\ell=\theta(A)$. (d) $K_s=\hat\theta(H_{\tau(s)})$; $M=\hat\theta(Q)$ contains $\ell^*=\{Z\}\cup\{\text{unmarked}\}$; a line $N\ne\ell$ through $X_s$ is $\theta$ of a point of $\theta(X_s)=\lambda_{\tau(s)}$ other than $A$. $\square$

For the three hats in a conic frame the only deleted flag is $(Z,Z^\perp)$ (an absolute point loses its loop), and the links $H_0\mathrel{\mathrm{I}}K_1$, $H_1\mathrel{\mathrm{I}}K_0$ make $H_0$ and $H_1$ absolute.

**Corollary 1.7 (Folding the hats).** \[new; proof and computer\] For every odd prime power $q\ge3$ the polarity graph of the four-hat conic frame is a graph of diameter $2$ and maximum degree $q+2$ on $q^2+q+6$ vertices; that of the three hats has $q^2+q+5$ vertices.

*Proof.* Theorem 1.4, Lemma 0.1 and Theorem 1.7 of `SYNTHETIC.md` (diameter $3$, degrees at most $q+2$). $\square$

By Proposition 1.6, this graph is the Erdős–Rényi graph of $\mathrm{PG}(2,q)$ with the edge $X_0X_1$ replaced by $X_0Z'$, plus five vertices: $Q$ joined to $Z$, to the $q-3$ unmarked points of $\ell$ and to the four hats; $H_s$ joined to the $q$ points of $\lambda_{\tau(s)}$ other than $A$; and $H_a$–$A$, $H_0$–$H_c$. (We checked by computer that this description is exactly the polarity graph, $q=3,\dots,13$: `conics/folded_direct.py`.) *Comparison* \[computer\]: at $q=13$ this is $188$ vertices at $(\Delta,D)=(15,2)$ for general graphs. The table of the general problem lists $187$ (E. Canale, 2012) in the UPC table and $190$ (2026) in the current Wikipedia table, read on 29 October 2026. So the folded four hats lie between the two and are not a record; at $\Delta=11,13$ ($q=9,11$: $96$ and $138$) they are far below the tabled $106$ and $162$. The three-hat fold at $q=13$ has $187$ vertices, the old tabled value; we do not know how Canale’s graph was built.

The four hats can also be built without changing any incidence of the plane (`research/plus3/plus3.tex`, Proposition “the four hats without changing the plane”): labels $a,1,2,3$, a $3$-cycle $s=(1\ 2\ 3)$, and the rotation carried by the hats ($H_i$ also on $AX_{s(i)}$, $K_i$ also through $X_{s^{-1}(i)}$). Its conic frame is $X_a=Z$, $X_2=Z'$, $\{X_1,X_3\}$ conjugate, with $\tau=(1\ 3)$, which inverts $s$.

**Proposition 1.8 (Self-polar four hats on an unchanged plane).** \[new; proof and computer\] In this conic frame the zero-change four-hat structure is self-polar, with $H_x\leftrightarrow K_{\tau(x)}$ and $Q\leftrightarrow M$. Its polarity graph is the Erdős–Rényi graph of $\mathrm{PG}(2,q)$, with *no edge changed*, plus five vertices: a graph of diameter $2$ and maximum degree $q+2$ on $q^2+q+6$ vertices.

*Proof.* The same check as in Lemma 1.3, rule by rule over the table of the cited proposition; the only new pairs are the extra incidences, and $(H_i,AX_{s(i)})$ goes to $(X_{\tau s(i)},K_{\tau(i)})$, which is the extra incidence of $K_{\tau(i)}$ because $s^{-1}\tau=\tau s$. No incidence of the plane is changed, so the old part of the polarity graph is the Erdős–Rényi graph. $\square$

*Computer.* `conics/zero_polar.py`, $q=3,\dots,13$ (polarity, diameter $3$, old part of the fold equal to the Erdős–Rényi graph, fold of diameter $2$).

So, in the language of the general problem: *the Erdős–Rényi graph of $\mathrm{PG}(2,q)$, $q$ odd, has room for five more vertices at maximum degree $q+2$ and diameter $2$*, and the five vertices are the folded hats. We have not searched the literature on extensions of polarity graphs; the count $q^2+q+6$ is below the tabled values except at $\Delta=15$, as said above.

## 1.4 An explicit regular version

In the four-hat structure the elements of degree $q+1$ (the deficient ones) are the points of $\Pi$ off $\ell$, other than $A$, on the lines $AY$ with $Y$ unmarked, and dually (`SYNTHETIC.md`, Lemma 1.4). `SYNTHETIC.md` completes the structure by any perfect matching of non-incident deficient pairs (König). The conic gives one.

**Proposition 1.9 (The polarity completes the hats).** \[new; proof and computer\] In a conic frame (three or four hats), let $p$ be a deficient point. If $p\notin\mathcal{C}$ put $\mu(p)=p^\perp$; if $p\in\mathcal{C}$, let $p^*$ be the second point of $\mathcal{C}$ on the line $Ap$ and put $\mu(p)=(p^*)^\perp$, the tangent at $p^*$. Then $\mu$ is a bijection from the deficient points onto the deficient lines with $p\mathrel{\not\mathrel{\mathrm{I}}}\mu(p)$, so adding the flags $(p,\mu(p))$ makes the structure $(q+2)$-regular (still of diameter $3$). The completed structure is again self-polar.

*Proof.* Let $p$ be deficient, on $AY$ with $Y\in\ell$ unmarked. $p^\perp$ does not pass through $A$ (as $p\notin\ell$), is not $\ell$ (as $p\ne A$), and meets $\ell=A^\perp$ in the pole of the line $pA=AY$. By Proposition 1.1, $AY=(Y^\tau)^\perp$, so this pole is $Y^\tau$. The marked set is $\tau$-invariant, so $Y^\tau$ is unmarked and $p^\perp$ is deficient. If $p\in\mathcal{C}$, the line $AY$ is not a tangent (the tangents from $A$ are $AZ$, $AZ'$ and $Z,Z'$ are marked in the four hats; in the three hats $Z'$ is unmarked, but $AZ'$ meets $\mathcal{C}$ only in $Z'\in\ell$, which is not deficient), so $AY$ is a secant and $p^*\ne p$ is deficient too, $p^*\notin\ell$; its tangent $(p^*)^\perp$ meets $\ell$ in $Y^\tau$ as before and does not contain $p$. The map $p\mapsto p^\perp$ is injective, and on $\mathcal{C}$ we composed it with the involution $p\mapsto p^*$ of the deficient points of $\mathcal{C}$, so $\mu$ is injective; the numbers of deficient points and lines are equal. Self-polarity: $\hat\theta$ maps the added flag $(p,p^\perp)$ to itself and $(p,(p^*)^\perp)$ to $(p^*,p^\perp)$, the added flag of $p^*$. $\square$

*Computer.* `conics/polar_frames.py` for $q=3,\dots,13$, and independently squad card `c3` ($24$ instances, $q=3,\dots,13$; the number of deficient points on $\mathcal{C}$ varies with $X$, from $0$ to $12$ at $q=13$). In the folded graph the added flags $(p,p^\perp)$ are loops, so the regular bipartite version does not give a regular graph of diameter $2$.

## 1.5 Does a conic allow more hats?

*The question in polar terms.* By Corollary 1.7 a self-polar extension of $\mathrm{PG}(2,q)$ by $k$ new points and $k$ new lines, of maximum degree $q+2$ and diameter $3$, is the same as an extension of the Erdős–Rényi graph by $k$ vertices of diameter $2$ in which any two points have a common line; the four hats are $k=5$, and five hats would be $k=6$.

*Heuristic: what the conic cannot change* \[heuristic\]. For large $q$, any extension by a few new elements is a *copy configuration* (`research/plus3/plus3.tex`, Theorem 3.4): every new point copies an old point and every new line an old line, and the line joining two copied points must itself be copied or carry a deleted flag. A conic offers a second natural set of points to copy, an arc. But $k$ copied points on a conic have $\binom k2$ joining lines (secants), all of which must be copied or broken; on a line the join is one line ($\ell$, copied by $M$). So collinear marked points are forced, and the conic can only choose *which* points of $\ell$ are marked and how the gadget is wired. Theorem 1.4 says that the conic chooses them so that the structure is self-polar; it does not create room for a fifth hat.

*Computer* \[computer\]:

(1) *Hat model at conic frames* (`conics/sat_hatmodel.py`, the model of `research/plus2/sat_gadget.py`: bulk incidences fixed, every incidence of the gadget free, degree $\le q+2$, diameter $3$). Five hats at $Z$ and two conjugate pairs, and six hats at $Z,Z'$ and two conjugate pairs, one $Q$ and one $M$: UNSAT for every choice of the pairs, $q=5,7,9,11,13$, with and without imposing self-polarity ($35$ five-hat and $35$ six-hat frames, $140$ runs, each under $4$ s; `conics/hatmodel_conic.out`). The four-hat conic frame is SAT in all these runs (control).

(2) *All self-polar extensions at $q=5$* (`conics/sat_polar.py`): new points and new lines tied by the conic polarity, all incidences of the new elements free, no change to the plane. $k=5$: SAT. $k=6$ (five hats): UNSAT. The search is split soundly by the orbit of the conic group $\mathrm{PGL}(2,5)$ that contains the point most often copied (conic point, external, internal) and the number $r$ of lines through it used by one new point; see `conics/k6_q5_E0.out` for the cases and times.

Earlier work, which this note does not repeat, ruled out five hats in the hat model at default and random frames for $q=4,\dots,13$, and $+3$ without changes for $q\ge42$ (`research/plus2/REPORT.md`, `research/plus3/plus3.tex`).

# 2. Generalized quadrangles

## 2.1 The analogues

In a generalized quadrangle of order $(s,t)$:

- an *ovoid* is a set of $st+1$ pairwise non-collinear points meeting every line once, a *partial ovoid* a set of pairwise non-collinear points, an *$m$-ovoid* a set meeting every line in $m$ points, and a *weighted* $m$-ovoid a multiset doing so; dually spreads and covers \[standard\];

- in $Q(4,q)$ the elliptic quadric sections $Q^-(3,q)$ are ovoids for every $q$ (and every ovoid of $Q(4,p)$, $p$ prime, is one \[BGS06\]); a plane section of $Q(4,q)$ that is a conic is a set of $q+1$ pairwise non-collinear points, the closest analogue of a conic *inside* the quadrangle; in $W(q)$, $q$ odd, there is no ovoid, and the elliptic quadrics of $\mathrm{PG}(3,q)$ (ovoids of the space, not of $W(q)$) are what the lab uses \[standard\];

- $W(q)$ has a polarity if and only if $q=2^{2e+1}$; its absolute points form the Suzuki–Tits ovoid and its absolute lines a spread \[VM98\] \[standard\]. This is the analogue of “conic $=$ absolute points”. For $q$ odd there is none: $W(q)$ and $Q(4,q)$ are dual and not isomorphic.

## 2.2 Where they appear in Theorems A–C

\[restatement\] Theorem B (`SYNTHETIC.md`, Theorem 2.2) adds clones over a weight $w$ on the points and shadow lines over a multiset $\mathcal{M}$ of lines; for a regular result $w$ must be a weighted $(\Delta-s-1)$-ovoid and $\mathcal{M}$ a weighted $(\Delta-t-1)$-cover. So the ovoid-like object is exactly the place where clones go, and the spread-like object where shadow lines go:

<div class="center">

| cells                             | quadrangle       | clones on                                             | shadow lines over            | conic-like content                                 |
|:----------------------------------|:-----------------|:------------------------------------------------------|:-----------------------------|:---------------------------------------------------|
| $(q+1+j,4)$, $q$ even             | $W(q)$           | $j\times$ an ovoid                                    | $j\times$ a spread           | ovoid (elliptic quadric or Tits)                   |
| Theorem A: $(11,4),(13,4),(15,4)$ | $\mathrm{AS}(q)$ | $\mathcal{E}_1\cup\mathcal{E}_2$ (weighted $2$-ovoid) | none                         | two elliptic quadrics; pairs of conics (Prop. 2.1) |
| Prop. C: $(16,4)$                 | $W(13)$          | a $2$-ovoid                                           | $2\times$ a spread           | union of two elliptic quadrics (Ebert’s partition) |
| $(7,4)$: 359                      | $Q(4,5)$         | an ovoid ($Q^-(3,5)$)                                 | $21$ lines, a partial spread | ovoid; partial spread at Tallini’s bound           |

</div>

The limits are also conic-like statements: for $q$ odd, $W(q)$ has no ovoid and $Q(4,q)$ no spread, which is why $\mathrm{AS}(q)$ and weights are used at $\Delta=q+2$; on $Q(4,q)$ with one ovoid of clones the shadow lines form a partial spread (or nearly), so at most $q^2-q+2$ of them (Tallini’s bound $q^2-q+1$ for partial ovoids of $W(q)$, `POLISHED.md` Remark 3.5), and the lab’s searches found $52,72,92$ at $q=9,11,13$ against the $61,97,141$ needed to beat Theorem A (`research/gq4x/REPORT.md`). Large partial ovoids of $W(3,q)$ in the literature \[CDPS22\] are far smaller than this.

## 2.3 Theorem A as a statement about pairs of conics

Theorem A (`POLISHED.md` §4) works in $\mathrm{PG}(3,q)$, $q$ odd, with the symplectic form $\beta(u,v)=u_0v_1-u_1v_0+u_2v_3-u_3v_2$, the point $x=(1{:}0{:}0{:}0)$, a non-square $\varepsilon$ and the elliptic quadrics $\mathcal{E}_1: 2X_0X_1=X_2^2-\varepsilon X_3^2$ and $\mathcal{E}_2: 2\varepsilon X_0X_1=X_2^2-\varepsilon X_3^2$, both through $x$ with tangent plane $x^\perp$. The lines of $\mathrm{AS}(q)$ not through $x$ are the totally isotropic lines $L\not\ni x$ minus their point $z$ in $x^\perp$, and $L$ lies in the plane $z^\perp$, which contains $x$.

**Proposition 2.1.** \[restatement; proof and computer\] For every point $z\ne x$ of $x^\perp$, the plane $z^\perp$ meets $\mathcal{E}_1$ and $\mathcal{E}_2$ in two conics $\mathcal{C}_1(z),\mathcal{C}_2(z)$ through $x$ with the same tangent $xz$ at $x$, and from the point $z$ of this common tangent every other line of $z^\perp$ through $z$ is a secant of one conic and a passant of the other, or a tangent of both. Equivalently (because every line of $\mathrm{AS}(q)$ of the second kind lies in exactly one such plane, and the fibres through $x$ meet each quadric once), $\mathbf 1_{\mathcal{E}_1\setminus x}+\mathbf 1_{\mathcal{E}_2\setminus x}$ is a weighted $2$-ovoid of $\mathrm{AS}(q)$: this is Theorem A.

*Proof.* A plane through $x$ other than $x^\perp$ meets an elliptic quadric through $x$ with tangent plane $x^\perp$ in a conic through $x$ whose tangent at $x$ is the plane’s intersection with $x^\perp$; here that is the line $xz$, as $x,z\in z^\perp\cap x^\perp$. The lines of $z^\perp$ through $z$ other than $xz$ are the totally isotropic lines through $z$ not through $x$; the discriminant computation of `POLISHED.md` (proof of Theorem 4.1) shows that the line $\ell(a_0,w_0;d)$ meets $\mathcal{E}_\kappa$ in $1+\chi(\kappa)\chi\bigl(N(d)(a_0-a^*)\bigr)$ points with the same $a^*$ for both quadrics and $\chi(\kappa_1)=-\chi(\kappa_2)$; this is the secant/passant swap. $\square$

*Computer.* Squad card `c5` checked (a) both sections are conics through $x$, (b) $xz$ is tangent to both, (c) the count $2$ and (d) the secant/passant/tangent pattern, for every $z$ at $q=3,5,7,11,13$ ($412$ pairs), for every non-square $\varepsilon$ ($\varepsilon=1$ fails, as a control), and re-checked the line form of Theorem A by enumerating all totally isotropic lines.

So the weighted $2$-ovoid of Theorem A is a family of *complementary conic pairs*, one pair in each plane $z^\perp$, all through $x$ and sharing their tangent there; the clone of a point $p\in\mathcal{E}_i\setminus x$ stands on the $q+2$ lines through $p$, and every line of $\mathrm{AS}(q)$ gains two clones because each line through $z$ is a secant of exactly one conic of the pair, or a tangent of both.

## 2.4 The polarity picture: $W(2^{2e+1})$

**Proposition 2.2.** \[restatement; proof\] Let $q=2^{2e+1}$, $\theta$ a polarity of $W(q)$, $\mathcal{O}$ its absolute points (a Suzuki–Tits ovoid) and $\Sigma$ its absolute lines (a spread). The structure $W(q)[\,j\mathbf 1_\mathcal{O},\ j\Sigma\,]$ of Theorem B ($j$ clones of every point of $\mathcal{O}$, $j$ shadow lines over every line of $\Sigma$, stand-ins original) is self-polar, with the $i$-th clone of $p\in\mathcal{O}$ exchanged with the $i$-th shadow line over $\theta(p)\in\Sigma$. Its polarity graph has diameter at most $3$, maximum degree $q+1+j$ and $(q+1+j)(q^2+1)$ vertices.

*Proof.* A flag (clone of $p$, $L$) with $L\ni p$ goes to $(\theta(L),\text{shadow over }\theta(p))$, and $\theta(L)$ lies on $\theta(p)$; dually for shadow lines. Theorem B gives diameter $4$ and Lemma 0.1 diameter $3$. $\square$

At $q=8$ this gives $585,650,715$ for $j=0,1,2$, which are the tabled values of the general problem at $(9,3),(10,3),(11,3)$ (Wikipedia table, read 29 October 2026); we have not checked the provenance of those graphs, and expect them to be of this kind. For $j=3$ it gives $780<810$. So in quadrangles the polarity picture reproduces known values and gives nothing at the lab’s (odd $q$) cells, where no polarity exists.

# 3. Generalized hexagons

## 3.1 The analogues

\[standard\] In a generalized hexagon of order $(q,q)$ with $N=(q+1)(q^4+q^2+1)$ points: a *distance-$2$ ovoid* is a set of $q^4+q^2+1$ points meeting every line once (pairwise non-collinear; known only for $q=2,3,4$); a *distance-$3$ ovoid* (an *ovoid*) is a set of $q^3+1$ pairwise opposite points; dually spreads. For the split Cayley hexagon $H(q)\subset Q(6,q)$, two points are opposite iff they are not orthogonal, so partial ovoids of $H(q)$ are partial ovoids of the polar space $Q(6,q)$; ovoids exist for $q=3^h$, not for $q$ even \[Th81\] or $q$ prime $\ge5$ \[BGS06\]. The *Hermitian spread* (the lines of $H(q)$ in a hyperplane meeting $Q(6,q)$ in an elliptic $Q^-(5,q)$) exists for every $q$ \[Th80\]. $H(q)$ has a polarity iff $q=3^{2e+1}$; its absolute points form the Ree–Tits ovoid and its absolute lines a spread \[VM98\]. The conic-like partial ovoids are the sections $Q^-(3,q)$ ($q^2+1$ points, every $q$; their plane sections are conics) and, as found by the lab’s squads, unions of conics through one point with a common tangent there (§3.3).

## 3.2 Theorem D

\[restatement\] Theorem D (`SYNTHETIC.md` §3) doubles $H(q)$ along levels built from a *spread* $\Sigma$, one line $v\in\Sigma$ and an exact whisker set. The spread plays the role that the special line plays for the hats: the components of the doubled set are the ball of radius $2$ about $v$ and one “broom” per spread line, and the ceiling $q|\mathcal A_0|+2(q^3+1)=2N$ is reached because every element outside $\mathcal A_0$ sees exactly one element of it. For odd $q$ the whiskers come from $q^2-1$ further Hermitian spreads through $v$ (with $\Sigma$, $q^2$ spreads pairwise meeting only in $v$), so the whole configuration is cut out by elliptic hyperplane sections; we found no conic-level description beyond this. The levels are not invariant under a polarity (they contain spread lines but not the corresponding ovoid points), so the folding of §0.2 does not apply to Theorem D as it stands.

*A self-polar doubling* \[new; proof\]. For $q=3^{2e+1}$ take the polarity $\theta$, its Ree–Tits ovoid $\mathcal{O}$ and absolute spread $\Sigma$, and the single level $\mathcal A_0=\mathcal{O}\cup\Sigma$. Its components are the $q^3+1$ flags $(p,\theta(p))$ (trees of diameter $1$), a point off $\mathcal{O}$ is on at most one line of $\Sigma$ and a line off $\Sigma$ has at most one point of $\mathcal{O}$, so conditions (L0) and (C) of `SYNTHETIC.md` §3.1 hold and the doubling with $m$ versions has diameter $6$, maximum degree $q+m$ and $2N+2(m-1)(q^3+1)$ elements. It is self-polar, so it folds to a graph of diameter $5$ with $N+(m-1)(q^3+1)$ vertices: $392$ at $(5,5)$ for $q=3$, $m=2$, far below the tabled $650$. Not a record; recorded only because it is the hexagon analogue of Corollary 1.7.

## 3.3 The diameter-7 freed sets

\[restatement, with one squad computation\] The diameter-$7$ constructions (`SYNTHETIC.md` §4) free the incidences of a matching at a set $R$ of points. With a duality ($q=3^h$) any segment set may be freed, and the point set of a spread (Hermitian, or the Ree–Tits spread when $q=3^{2e+1}$) is the largest one; with arbitrary matchings $R$ must be non-collinear and the matching a local duality, which is easy when $R$ is a partial ovoid. So the size of the records at $(7,7),(9,7),(10,7),(13,7)$ is governed by large partial ovoids of $H(q)$, i.e. of $Q(6,q)$. The conic-like ones are:

- the $q^2+1$ points of an elliptic section $Q^-(3,q)$ (`D7_HEXAGON.md`, Corollary 9.1, every $q$);

- *conic fans*: a point $e$ and $k$ conics through $e$ whose planes share one tangent line at $e$, $1+qk$ points; the points opposite $e$ form an affine space $\mathrm{AG}(5,q)$ in which opposition is $Q'(x-x')\ne0$ for a quadratic form $Q'$, and each conic is an affine line with non-square $Q'$-direction (`research/d13D7/REPORT.md` §3, $1+11\cdot29=320$ at $q=11$);

- the record sets themselves (72, 288, 217 and 756 pairwise opposite points at $q=5,7,8,11$, plus a few mirrored points) come from searches and, at $q=7,11$, from orbits of the Weyl group $W(E_7)$.

*Squad computation* \[computer\]: card `c7` rebuilt the conic fans for $q=5,7$ (direct check of opposition on all pairs; the $q+1$ points of each fan line with $e$ form a conic of a plane) and searched for large fans with one direction: at $q=5$ the compatibility graph on the $625$ cosets has clique number exactly $7$ (exact branch and bound, confirmed by SAT, for every one of the $300$ non-square directions), so single-direction fans have at most $1+5\cdot7=36$ points; at $q=7$ a tabu search found $15$ lines, $106$ points. The records use $72$ and $288$ pairwise opposite points at these $q$, so at small $q$ the conic fans are not competitive; they become useful only at $q=11$ (320 points), and there the record set (756) is a Weyl-group orbit, not a fan.

*What the hexagon offers that the plane does not* \[heuristic\]. In the plane the conic’s polarity is what makes the hats self-polar; in the hexagon a polarity exists only for $q=3^{2e+1}$, outside the lab’s cells (which use $q=5,7,8,9,11,13$), and the diameter-$7$ layouts with an odd number of copies are self-polar only if one copy is mapped to itself, which needs such a polarity. So the conic-as-polarity picture does not reach the hexagon records, and the conic-as-ovoid picture is already what the records use.

# 4. Summary: what is new

- **New** (proof and computer): the conic frame of the hats (Definition 1.2); the hats in a conic frame are self-polar (Theorem 1.4, Lemma 1.3), and the conic frame is the only frame with this polarity (Remark 1.5; computer for $q=5,7$); the gadget read as a change of the conjugacy relation (Proposition 1.6); the explicit regular completion by the polarity (Proposition 1.9); the folded graphs of diameter $2$ (Corollary 1.7); the self-polar doubling of $H(3^{2e+1})$ (§3.2).

- **New** (computer): no five or six hats in the hat model at any conic frame for $q\le13$; no self-polar five-hat extension of $\mathrm{PG}(2,5)$ without changes.

- **Restatements**: the dictionary of §0; Theorem A as complementary conic pairs (Proposition 2.1); where ovoids, partial ovoids and spreads sit in Theorems A–C, D and the $D=7$ freed sets; the $W(8)$ polarity values (Proposition 2.2).

- **Records**: none. No conic-based choice beat a lab value; the folded graphs are below the current general tables.

# Appendix A. Files and checks

In `research/synthetic/conics/`: `pg2.py` ($\mathrm{PG}(2,q)$, the conic, the hat rules), `selfpolar.py` and `polar_frames.py` (Theorem 1.4, Corollary 1.7, Proposition 1.9, all polarity types; outputs `*.out`), `sat_hatmodel.py` and `run_hatmodel.py` (hat model at conic frames; `hatmodel_conic.out`), `sat_polar.py` and `run_cases.sh` (self-polar extensions; `k6_q5_E0.out`). Squad round `research/squads/conics-r1/` (brief, eight cards, scoreboard), logged in `research/squads/LOG.md`. Python with `python-sat` (CaDiCaL 1.5.3).

<div class="thebibliography">

99 G. Araujo-Pardo and N. López, On new record graphs close to bipartite Moore graphs, Graphs Combin. **38** (2022), Paper 110; arXiv:2005.02427. S. Ball, P. Govaerts, L. Storme, On ovoids of parabolic quadrics, Des. Codes Cryptogr. **38** (2006) 131–145. M. Ceria, J. De Beule, F. Pavese, V. Smaldore, On large partial ovoids of symplectic and Hermitian polar spaces, J. Combin. Des. **31** (2023) 5–22; arXiv:2203.04553. S. E. Payne and J. A. Thas, Finite Generalized Quadrangles, 2nd ed., EMS, 2009. J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A **29** (1980) 87–93. J. A. Thas, Ovoids and spreads of finite classical polar spaces, Geom. Dedicata **10** (1981) 135–143. H. Van Maldeghem, Generalized Polygons, Birkhäuser, 1998.

</div>
