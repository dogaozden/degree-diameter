<!-- Generated from SYNTHETIC.tex by make_md.py; the figures are in SYNTHETIC.pdf. -->

# Adding points and lines to generalized polygons: the constructions without coordinates

*Degree–diameter lab, 28 October 2026. Markdown copy of `SYNTHETIC.tex`; the PDF has the figures.*

*Abstract.* Written for Gabriela Araujo-Pardo and Ignacio López. Each construction of the lab is described here only in terms of incidence: points, lines, the lines through a point, the points of a line, flags, anti-flags, collinearity, distances in the incidence graph, and configurations (ovoids, spreads, $m$-ovoids, whiskers) defined by their combinatorial properties. For each construction we say what is chosen in the starting geometry, which incidences are deleted or moved, which new points and lines are added and exactly what they are incident with, which pairs of elements stop being collinear or concurrent and how the new elements repair this, and why the diameter and the degrees are as claimed. Section 1 treats the diameter-$3$ constructions in a projective plane: the three hats of Araujo-Pardo and López and our four hats, side by side and in the same words. Sections 2– 4 treat diameters $4$, $6$ and $7$ in generalized quadrangles and hexagons. The sections can be read independently.

*Sources.* Everything here is taken from the lab’s notes: `research/theorems/POLISHED.md` (coordinates and complete proofs of all results below), `research/geometry/geometry.tex`, `research/plus2/coords/coords.tex`, `research/theorems/D7_HEXAGON.md` and the joint draft `research/paper/joint.tex`. No new result is claimed. Every combinatorial statement in Section 1 was checked by a program that builds both structures from the rules below on a plane given only by its incidence relation (`research/synthetic/checks/check_d3.py`: $\mathrm{PG}(2,q)$ for $q=3,4,5,7$, the non-Desarguesian nearfield plane of order $9$, and agreement with the coordinate version for $q\le 9$). The other sections were checked in the same way on small quadrangles and hexagons (Appendix A).

# 0. Conventions

An *incidence structure* consists of points, lines and a symmetric incidence relation $\mathrel{\mathrm{I}}$ between points and lines. Points and lines are *elements*. A *flag* is an incident point–line pair, an *anti-flag* a non-incident one. The *degree* of an element is the number of elements incident with it. Two distinct points are *collinear* if some line contains both, and two distinct lines are *concurrent* if some point lies on both. We do *not* assume that two points lie on at most one line: after points and lines are added, two points may have several common lines, and two lines may have the same points.

The *incidence graph* has the elements as vertices and the flags as edges; it is bipartite. Distances $d(x,y)$ and the diameter are taken in it. So two points are at distance $2$ when they are collinear, a point and a line are at distance $3$ when they form an anti-flag and some point of the line is collinear with the point, and so on.

A *generalized $n$-gon* is an incidence structure whose incidence graph has diameter $n$ and girth $2n$; elements at distance $n$ are *opposite*. It has *order $(s,t)$* if every line has $s+1$ points and every point is on $t+1$ lines. Projective planes are the generalized $3$-gons, generalized quadrangles the $4$-gons, generalized hexagons the $6$-gons. Write $n_b(\Delta,D)$ for the largest number of elements of an incidence structure with all degrees at most $\Delta$ and diameter at most $D$ (the bipartite degree–diameter problem). A generalized $n$-gon of order $(q,q)$ attains the counting (Moore) bound for $n_b(q+1,n)$. When $q+1$ is not a prime power, no generalized polygon of order $(q+1,q+1)$ is known, and every construction below starts from a generalized polygon of order $(q,q)$ (or $(q-1,q+1)$) and adds points and lines so that the maximum degree becomes $q+2$ (or more) while the diameter stays the same. Table 1 is a summary.

| §   | start                                              | chosen configuration                                                                                                              | changed incidences                                                       | added elements                                        |
|:----|:---------------------------------------------------|:----------------------------------------------------------------------------------------------------------------------------------|:-------------------------------------------------------------------------|:------------------------------------------------------|
| 1   | projective plane of order $q$; $D=3$, $\Delta=q+2$ | an anti-flag $(A,\ell)$ and $3$ or $4$ points of $\ell$                                                                           | $1$ flag deleted (three hats); $4$ deleted and $3$ added (four hats)     | $4+4$ or $5+5$: hat points and hat lines, $Q$ and $M$ |
| 2   | generalized quadrangle; $D=4$                      | a weighted $m$-ovoid and a weighted $m'$-cover (two elliptic quadrics in $\mathrm{AS}(q)$; a $2$-ovoid and a spread of $W(q)$; …) | none                                                                     | clones of points and shadow lines                     |
| 3   | generalized hexagon of order $(q,q)$; $D=6$        | a spread $S$, a line $v\in S$, an exact whisker set                                                                               | none; every element of three nested sets is replaced by several versions | $(m-1)\sum_k m^k|\mathcal{A}_k|$ versions             |
| 4   | $2r+1$ copies of a generalized hexagon; $D=7$      | bijections from the points of one copy to the lines of another; freed sets (segment sets, local dualities)                        | the incidences between copies at the freed points are deleted            | hub points and hub lines                              |

*Table 1.* The constructions at a glance.

Distances can be read off from collinearity alone:

**Lemma 0.1 (Diameter in incidence terms).** Let $\mathcal{S}$ be an incidence structure in which every element is incident with at least one element.

(a) $\operatorname{diam}\mathcal{S}\le 3$ if and only if any two points are collinear and any two lines are concurrent.

(b) $\operatorname{diam}\mathcal{S}\le 4$ if and only if for every anti-flag $(p,L)$ some point of $L$ is collinear with $p$.

(c) $\operatorname{diam}\mathcal{S}\le 6$ if and only if for every anti-flag $(p,L)$ some point of $L$ is at distance at most $4$ from $p$.

(d) $\operatorname{diam}\mathcal{S}\le 7$ if and only if any two points, and any two lines, are at distance at most $6$.

*Proof.* For an even bound $D$: two points $p\neq p'$ are at distance at most $D$ as soon as $p$ is within $D-1$ of some line $L$ through $p'$ (if $p\mathrel{\mathrm{I}}L$ the distance is $2$); two lines likewise. For an odd bound $D$: an anti-flag $(p,L)$ is within distance $D$ as soon as $p$ is within $D-1$ of some point of $L$. Distances between a point and a line are odd and distances between two points or two lines are even, which gives the converses. $\square$

# 1. Diameter 3: hats in a projective plane

Let $\Pi$ be a projective plane of order $q$: any two points are on exactly one line, any two lines meet in exactly one point, and every element has degree $q+1$. For points $u\ne v$ we write $uv$ for the line joining them. Both constructions in this section keep all points and lines of $\Pi$, delete or move a few flags near a chosen anti-flag, and add a few points and lines. By Lemma 0.1(a) the diameter stays $3$ exactly when any two points remain collinear and any two lines remain concurrent; this is what has to be checked.

## 1.1 The frame

Fix an anti-flag $(A,\ell)$. Every line through $A$ meets $\ell$ in one point, and every point of $\ell$ is on one line through $A$. So the $q+1$ flags $(X,AX)$, $X$ a point of $\ell$, are the only incidences between the points of $\ell$ and the lines through $A$, and they match the points of $\ell$ with the lines through $A$. Both constructions change only some of these $q+1$ flags.

Choose distinct *marked* points $X_s$ on $\ell$, indexed by a label set $S$, and put $$\lambda_s = AX_s \qquad (s\in S).$$ One label $a\in S$ is distinguished, and $T=S\setminus\{a\}$. We write $$\ell^* = \{\text{points of } \ell\}\setminus\{X_t : t\in T\},\qquad \Lambda^* = \{\text{lines through } A\}\setminus\{\lambda_t: t\in T\}.$$ So $\ell^*$ contains $X_a$ and the $q+1-|S|$ unmarked points of $\ell$, and $\Lambda^*$ contains $\lambda_a$ and the $q+1-|S|$ lines joining $A$ to them. We call $A$, $\ell$, the $X_s$ and the $\lambda_s$ the *frame*.

- The construction of Araujo-Pardo and López \[AL20\] (*three hats*) uses three marked points: $S=\{0,1,a\}$, $T=\{0,1\}$.

- The *four hats* use four: $S=\{0,1,a,c\}$, $T=\{0,1,c\}$; this needs $q\ge 3$.

The labels $0,1,a,c$ are only names. The new elements are, for each $s\in S$, a *hat point* $H_s$ and a *hat line* $K_s$, and one more point $Q$ and one more line $M$.

## 1.2 The two constructions

Both constructions follow the same six rules. They differ in two permutations of $T$: the *links* $\pi$, a permutation of $T$ without fixed points, and the *rotation* $\rho$.

**Definition 1.1.** The incidence structure $\mathcal{S}$ has as points the points of $\Pi$, the point $Q$ and the hat points $H_s$; as lines the lines of $\Pi$, the line $M$ and the hat lines $K_s$; and exactly the following incidences.

(R1) The incidences of $\Pi$, except the flags $(X_s,\lambda_s)$, $s\in S$; and the flags $(X_t,\lambda_{\rho(t)})$, $t\in T$.

(R2) $H_s$ lies on every line of $\Pi$ through $X_s$ other than $\ell$ ($q$ lines, $\lambda_s$ among them).

(R3) $K_s$ contains every point of $\lambda_s$ other than $A$ ($q$ points, $X_s$ among them).

(R4) $M$ contains the points of $\ell^*$ and every hat point $H_s$.

(R5) $Q$ lies on the lines of $\Lambda^*$ and on every hat line $K_s$.

(R6) The *links*: $A\mathrel{\mathrm{I}}K_a$,  $H_a\mathrel{\mathrm{I}}\ell$, and $H_t\mathrel{\mathrm{I}}K_{\pi(t)}$ for $t\in T$.

|                | three hats \[AL20\]                                                                                                   | four hats                                                                                                                                           |
|:---------------|:----------------------------------------------------------------------------------------------------------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------|
| marked points  | $X_0,X_1,X_a$                                                                                                         | $X_0,X_1,X_a,X_c$                                                                                                                                   |
| flags deleted  | $(X_a,\lambda_a)$                                                                                                     | $(X_0,\lambda_0)$, $(X_c,\lambda_c)$, $(X_1,\lambda_1)$, $(X_a,\lambda_a)$                                                                          |
| flags added    | none                                                                                                                  | $(X_0,\lambda_c)$, $(X_c,\lambda_1)$, $(X_1,\lambda_0)$                                                                                             |
| $H_s$ lies on  | the $q$ lines through $X_s$ other than $\ell$;  $M$;  one link line                                                   | (same)                                                                                                                                              |
| $K_s$ contains | the $q$ points of $\lambda_s$ other than $A$;  $Q$;  one link point                                                   | (same)                                                                                                                                              |
| $M$ contains   | the $q-1$ points of $\ell$ other than $X_0,X_1$; $H_0,H_1,H_a$                                                        | the $q-2$ points of $\ell$ other than $X_0,X_1,X_c$; $H_0,H_1,H_a,H_c$                                                                              |
| $Q$ lies on    | the $q-1$ lines through $A$ other than $\lambda_0,\lambda_1$; $K_0,K_1,K_a$                                           | the $q-2$ lines through $A$ other than $\lambda_0,\lambda_1,\lambda_c$; $K_0,K_1,K_a,K_c$                                                           |
| links          | $A\mathrel{\mathrm{I}}K_a$, $H_a\mathrel{\mathrm{I}}\ell$, $H_0\mathrel{\mathrm{I}}K_1$, $H_1\mathrel{\mathrm{I}}K_0$ | $A\mathrel{\mathrm{I}}K_a$, $H_a\mathrel{\mathrm{I}}\ell$, $H_0\mathrel{\mathrm{I}}K_c$, $H_c\mathrel{\mathrm{I}}K_1$, $H_1\mathrel{\mathrm{I}}K_0$ |
| $\pi$, $\rho$  | $\pi=(0\ 1)$, $\rho=\mathrm{id}$                                                                                      | $\pi=\rho=\sigma=(0\ c\ 1)$: $0\mapsto c\mapsto 1\mapsto 0$                                                                                         |
| new elements   | $Q,H_0,H_1,H_a$; $M,K_0,K_1,K_a$                                                                                      | $Q,H_0,H_1,H_a,H_c$; $M,K_0,K_1,K_a,K_c$                                                                                                            |

*Table 2.* The two constructions, rule by rule. With $\rho=\mathrm{id}$, rule (R1) deletes and restores the flags $(X_t,\lambda_t)$, $t\in T$, so the three hats delete only $(X_a,\lambda_a)$.

So the three hats of \[AL20\] are $\mathcal{S}$ with $S=\{0,1,a\}$, $\pi=(0\ 1)$, $\rho=\mathrm{id}$, and the four hats are $\mathcal{S}$ with $S=\{0,1,a,c\}$ and $\pi=\rho=\sigma$. Table 2 puts the two side by side, and Figure 1 shows what rule (R1) and the links do to the flags between $\ell$ and the lines through $A$.

*Dictionary.* In \[AL20\] the plane is described from a flag $(P,L)$ (the point and line at infinity); $P_0$ is a point of $L$ other than $P$, and $L_0$ a line through $P$ other than $L$. In our names $P_0=A$, $L_0=\ell$, $(0,s)=X_s$, $[0,s]=\lambda_s$, $Q_0=Q$, $M_0=M$, $\widehat{(0,s)}=H_s$, $\widehat{[0,s]}=K_s$. By their Observation 1, the lines through $(0,s)$ other than $L_0$ are the $[t,s]$ and the points of $[0,s]$ other than $P_0$ are the $(t,s)$, so their edges $(\widehat{(0,j)},[t,j])$ and $(\widehat{[0,j]},(t,j))$ are rules (R2) and (R3). Their edges $(P,M_0)$ and $(M_0,(0,i))$, $i\ne 0,1$, together say that $M$ contains the points of $L_0$ other than $(0,0),(0,1)$, and with $(M_0,\widehat{(0,j)})$ this is (R4); dually $(L,Q_0)$, $(Q_0,[0,i])$ and $(Q_0,\widehat{[0,j]})$ give (R5). The edges $(P_0,\widehat{[0,a]})$, $(L_0,\widehat{(0,a)})$, $(\widehat{(0,0)},\widehat{[0,1]})$, $(\widehat{(0,1)},\widehat{[0,0]})$ are the links, and the deleted edge $((0,a),[0,a])$ is (R1). The flag $(P,L)$ plays no role in the construction: $P$ is one of the points of $\ell^*$ and $L$ one of the lines of $\Lambda^*$.

|                     |           |             |             |             |           |           |           |           |
|:--------------------|:---------:|:-----------:|:-----------:|:-----------:|:---------:|:---------:|:---------:|:---------:|
| three hats \[AL20\] |           |             |             |             |           |           |           |           |
|                     |  $\ell$   | $\lambda_0$ | $\lambda_1$ | $\lambda_a$ |    $M$    |   $K_0$   |   $K_1$   |   $K_a$   |
| $A$                 |           |  $\bullet$  |  $\bullet$  |  $\bullet$  |           |           |           | $\bullet$ |
| $X_0$               | $\bullet$ |  $\bullet$  |             |             |           | $\bullet$ |           |           |
| $X_1$               | $\bullet$ |             |  $\bullet$  |             |           |           | $\bullet$ |           |
| $X_a$               | $\bullet$ |             |             |   $\circ$   | $\bullet$ |           |           | $\bullet$ |
| $Q$                 |           |             |             |  $\bullet$  |           | $\bullet$ | $\bullet$ | $\bullet$ |
| $H_0$               |           |  $\bullet$  |             |             | $\bullet$ |           | $\bullet$ |           |
| $H_1$               |           |             |  $\bullet$  |             | $\bullet$ | $\bullet$ |           |           |
| $H_a$               | $\bullet$ |             |             |  $\bullet$  | $\bullet$ |           |           |           |

|           |           |             |             |             |             |           |           |           |           |           |
|:----------|:---------:|:-----------:|:-----------:|:-----------:|:-----------:|:---------:|:---------:|:---------:|:---------:|:---------:|
| four hats |           |             |             |             |             |           |           |           |           |           |
|           |  $\ell$   | $\lambda_0$ | $\lambda_c$ | $\lambda_1$ | $\lambda_a$ |    $M$    |   $K_0$   |   $K_c$   |   $K_1$   |   $K_a$   |
| $A$       |           |  $\bullet$  |  $\bullet$  |  $\bullet$  |  $\bullet$  |           |           |           |           | $\bullet$ |
| $X_0$     | $\bullet$ |   $\circ$   |  $\bullet$  |             |             |           | $\bullet$ |           |           |           |
| $X_c$     | $\bullet$ |             |   $\circ$   |  $\bullet$  |             |           |           | $\bullet$ |           |           |
| $X_1$     | $\bullet$ |  $\bullet$  |             |   $\circ$   |             |           |           |           | $\bullet$ |           |
| $X_a$     | $\bullet$ |             |             |             |   $\circ$   | $\bullet$ |           |           |           | $\bullet$ |
| $Q$       |           |             |             |             |  $\bullet$  |           | $\bullet$ | $\bullet$ | $\bullet$ | $\bullet$ |
| $H_0$     |           |  $\bullet$  |             |             |             | $\bullet$ |           | $\bullet$ |           |           |
| $H_c$     |           |             |  $\bullet$  |             |             | $\bullet$ |           |           | $\bullet$ |           |
| $H_1$     |           |             |             |  $\bullet$  |             | $\bullet$ | $\bullet$ |           |           |           |
| $H_a$     | $\bullet$ |             |             |             |  $\bullet$  | $\bullet$ |           |           |           |           |

*Table 3.* The *gadget*: all incidences among the frame and the new elements ($\bullet$ incident, $\circ$ a flag of $\Pi$ that was deleted). Every other incidence of a new element is with an element outside the frame, by rules (R2)– (R5). In both tables the block $\{X_t\}\times\{\lambda_t\}$ ($t\in T$) is the permutation matrix of $\rho$ and the block $\{H_t\}\times\{K_t\}$ is that of $\pi$: the identity and the transposition $(0\ 1)$ for the three hats, the $3$-cycle $\sigma$ twice for the four hats.

*\[Figure: see SYNTHETIC.pdf.\]*

*Figure 1.* The incidences between the points of $\ell$ and the lines through $A$ (squares are lines, circles points; black: kept flags of $\Pi$, dashed: deleted flags, red: new). In $\Pi$ they form a perfect matching, $X\leftrightarrow AX$. In $\mathcal{S}$ they still form a perfect matching, once the new point $H_a$ (which lies on $\ell$) is counted among the points of $\ell$ and the new line $K_a$ (which passes through $A$) among the lines through $A$: $X_a$ is now matched with $K_a$ and $\lambda_a$ with $H_a$. The three hats keep the other flags. The four hats replace the three flags $(X_t,\lambda_t)$, $t\in T$, by the cyclic shift $(X_t,\lambda_{\sigma(t)})$, the *rotation*. There are no other incidences between these points and lines.

## 1.3 What the new elements are: a crossed doubling of the frame

The hat point $H_s$ is a copy of $X_s$ that does not see $\ell$; the hat line $K_s$ is a copy of $\lambda_s$ that does not see $A$; and $(Q,M)$ is a copy of the anti-flag $(A,\ell)$ that does not see the elements $X_t$, $\lambda_t$, $t\in T$. This is how \[AL20\] prove that the diameter is $3$: their Observation 2 compares each hat vertex with the vertex it copies. In both constructions one has, more precisely: *$H_s$ is at the same distance from every point and line of $\Pi$ as $X_s$ is in $\Pi$, except from $X_s$ itself and, if $s\neq a$, from $\ell$; dually $K_s$ is at the same distance from every element of $\Pi$ as $\lambda_s$, except from $\lambda_s$ and, if $s\ne a$, from $A$* (checked by computer for $q\le 7$). The cleanest way to say all this is as a doubling of the frame, in the sense of Delorme \[D85a\], with one twist.

Let $\mathcal{F}$ be the set of frame elements $A$, $\ell$, $X_s$, $\lambda_s$ ($s\in S$), and give each $x\in\mathcal{F}$ a copy $x'$ of the same kind: $$A'=Q,\qquad \ell'=M,\qquad X_s'=H_s,\qquad \lambda_s'=K_s .$$ The *crossed doubling* $\mathcal{D}$ of the frame has the points and lines of $\Pi$ and these copies, and the following incidences: all incidences of $\Pi$; for $x\in\mathcal{F}$ and $y\notin\mathcal{F}$ with $x\mathrel{\mathrm{I}}y$, the incidence $x'\mathrel{\mathrm{I}}y$ (a copy sees the same elements outside the frame as its original); for $x,y\in\mathcal{F}$ with $x\mathrel{\mathrm{I}}y$, the incidence $x'\mathrel{\mathrm{I}}y'$ (copies see copies), except that each flag $(X_s,\lambda_s)$ is *crossed*: instead of $X_s'\mathrel{\mathrm{I}}\lambda_s'$ we put $X_s'\mathrel{\mathrm{I}}\lambda_s$ and $X_s\mathrel{\mathrm{I}}\lambda_s'$.

Reading off the neighbours of the copies: $H_s$ lies on $M$ (as $X_s\mathrel{\mathrm{I}}\ell$) and on the lines through $X_s$ other than $\ell$ (those other than $\lambda_s$ are outside $\mathcal{F}$; $\lambda_s$ by the crossing); $K_s$ contains $Q$ and the points of $\lambda_s$ other than $A$; $M$ contains the hat points and the unmarked points of $\ell$; $Q$ lies on the hat lines and the lines through $A$ other than the $\lambda_s$. Comparing with Definition 1.1:

**Proposition 1.2.** $\mathcal{S}$ is obtained from the crossed doubling $\mathcal{D}$ of the frame by

(i) adding the *patches* $X_a\mathrel{\mathrm{I}}M$, $Q\mathrel{\mathrm{I}}\lambda_a$, $A\mathrel{\mathrm{I}}K_a$, $H_a\mathrel{\mathrm{I}}\ell$ and $H_t\mathrel{\mathrm{I}}K_{\pi(t)}$ ($t\in T$);

(ii) deleting the flags $(X_s,\lambda_s)$, $s\in S$, and adding the flags $(X_t,\lambda_{\rho(t)})$, $t\in T$ (for the three hats: deleting $(X_a,\lambda_a)$).

So the question “what happens to the combinatorics when these points and lines are added” splits into two: what the doubling does (Lemma 1.3), and what the patches, the deletions and the rotation do (§1.4).

**Lemma 1.3.** Suppose $\ell$ has an unmarked point ($|S|\le q$). In the crossed doubling $\mathcal{D}$:

(a) $X_s$ and $\lambda_s$ have degree $q+2$; $A$, $\ell$, $Q$, $M$, $H_s$, $K_s$ have degree $q+1$; an element outside $\mathcal{F}$ has degree $q+2$ if it is on $\ell$ or on some $\lambda_s$ (a point), or passes through $A$ or some $X_s$ (a line), and degree $q+1$ otherwise.

(b) The pairs of points that are not collinear are exactly $$\{H_s,X_t\}\ (s\ne t)\qquad\text{and}\qquad\{H_s,Q\},$$ and the pairs of lines that are not concurrent are exactly $\{K_s,\lambda_t\}$ ($s\ne t$) and $\{K_s,M\}$.

*Proof.* (a) $X_s$ gains $K_s$ (crossing) and $\lambda_s$ gains $H_s$; $A$ and $\ell$ gain nothing, since their frame neighbours are copied together with them. $Q$ lies on $|S|$ hat lines and $q+1-|S|$ lines through $A$; $H_s$ on $M$ and $q$ lines; dually for $M$, $K_s$. A point outside $\mathcal{F}$ gains $M$ if it is on $\ell$ and $K_s$ if it is on $\lambda_s$ (at most one of these, as it is not $A$ or an $X_s$).

\(b\) Two points of $\Pi$ keep their common line. $Q$ and a point $u$ of $\Pi$: if $u=A$, use a line through $A$ outside $\mathcal{F}$ (there is one, as $|S|\le q$; for the four hats with $q=3$ there is none, and $\{Q,A\}$, $\{M,\ell\}$ are two more far pairs, repaired by the patches $Q\mathrel{\mathrm{I}}\lambda_a$ and $X_a\mathrel{\mathrm{I}}M$); if $Au$ is not a $\lambda_s$, use $Au$; if $u\neq A$ is on $\lambda_s$, use $K_s$. $H_s$ and a point $u\notin\ell$: use $uX_s$, which is not $\ell$. $H_s$ and $X_s$: a line through $X_s$ outside $\mathcal{F}$. $H_s$ and an unmarked point of $\ell$: $M$. Two hat points: $M$. This leaves $H_s$ and $X_t$ ($t\ne s$), whose only common line in $\Pi$ is $\ell$, which $H_s$ is not on, while $M\not\ni X_t$ and the other lines of $H_s$ meet $\ell$ only in $X_s$; and $H_s$ and $Q$, which have no common line ($Q$ is on no line through $X_s$ except possibly $\lambda_s$, and $Q\notin\lambda_s$; $Q\notin M$). The statement for lines is the same argument with points and lines exchanged; $\mathcal{D}$ is built from $\Pi$ and the frame by rules that are symmetric under this exchange. $\square$

So the copies cost nothing among the old points: no two points of $\Pi$ become non-collinear and no two lines of $\Pi$ stop meeting. The failures all involve a copy, and they come from paths of length $2$ inside the frame: $X_s-\ell-X_t$ (the copy $H_s$ of $X_s$ does not see $\ell$, and the original $X_t$ does not see the copy $M$ of $\ell$) and $X_s-\lambda_s-A$ (the crossing removes the copy $H_s-K_s-Q$ of this path). For Delorme’s doubling without crossing, the hat lemma (`POLISHED.md`, Lemma 1.3) says that a set of elements of a projective plane can be doubled without changing the diameter only if each of its connected components is a single element or a flag; the frame contains the paths $\ell,X_s,\lambda_s,A$, so some patching is unavoidable. Lemma 1.3(a) also says that the doubling leaves exactly one free incidence at each of the $2|S|+4$ elements $A,\ell,Q,M,H_s,K_s$, and none at $X_s$, $\lambda_s$.

## 1.4 The patches, the deletions and the rotation

The patches of Proposition 1.2(i) spend the free incidences of $A,\ell,Q,M,H_s,K_s$, one each. The far pairs of Lemma 1.3(b) are repaired as follows (a pair $\{H_s,X_t\}$ always has $s\neq t$):

<div class="center">

| far pair in $\mathcal{D}$                          | common line in $\mathcal{S}$ | because of                                                                                          |
|:---------------------------------------------------|:-----------------------------|:----------------------------------------------------------------------------------------------------|
| $\{H_s,X_a\}$                                      | $M$                          | patch $X_a\mathrel{\mathrm{I}}M$                                                                    |
| $\{H_a,X_t\}$                                      | $\ell$                       | patch $H_a\mathrel{\mathrm{I}}\ell$                                                                 |
| $\{H_t,X_{\pi(t)}\}$, $t\in T$                     | $K_{\pi(t)}$                 | link $H_t\mathrel{\mathrm{I}}K_{\pi(t)}$ (and $X_{\pi(t)}\mathrel{\mathrm{I}}K_{\pi(t)}$)           |
| $\{H_t,X_{\sigma^{-1}(t)}\}$, $t\in T$ (four hats) | $\lambda_t$                  | rotation $X_{\sigma^{-1}(t)}\mathrel{\mathrm{I}}\lambda_t$ (and $H_t\mathrel{\mathrm{I}}\lambda_t$) |
| $\{H_a,Q\}$                                        | $\lambda_a$                  | patch $Q\mathrel{\mathrm{I}}\lambda_a$ (and $H_a\mathrel{\mathrm{I}}\lambda_a$)                     |
| $\{H_t,Q\}$, $t\in T$                              | $K_{\pi(t)}$                 | link $H_t\mathrel{\mathrm{I}}K_{\pi(t)}$                                                            |

</div>

The far pairs of lines are repaired dually: $\{K_s,\lambda_a\}$ by $Q$, $\{K_a,\lambda_t\}$ by $A$, $\{K_{\pi(t)},\lambda_t\}$ by $H_t$, $\{K_t,\lambda_{\sigma(t)}\}$ by $X_t$ (four hats), $\{K_a,M\}$ by $X_a$, $\{K_{\pi(t)},M\}$ by $H_t$.

*Why the three hats need no rotation and the four hats do.* The pairs $\{H_s,X_t\}$ with $s=a$ or $t=a$ are repaired by $\ell$ and $M$. What remains is $\{H_t,X_u\}$ for $t\ne u$ in $T$: each hat point $H_t$ must reach the $|T|-1$ points $X_u$, $u\in T\setminus\{t\}$, and it has one free incidence, which goes to a link. For the three hats $|T|-1=1$ and the link $H_t\mathrel{\mathrm{I}}K_{\pi(t)}$ suffices. For the four hats $|T|-1=2$: the link reaches $X_{\sigma(t)}$, and $X_{\sigma^{-1}(t)}$ is reached through $\lambda_t$, which already carries $H_t$, after the rotation has moved $X_{\sigma^{-1}(t)}$ onto $\lambda_t$. Hence $\rho=\pi=\sigma$: $\rho^{-1}(t)$ must be the element of $T\setminus\{t\}$ that $\pi$ does not reach. (Dually each hat line $K_t$ meets $\lambda_{\sigma(t)}$ in $X_t$ and $\lambda_{\sigma^{-1}(t)}$ in $H_{\sigma^{-1}(t)}$.) With $|T|=4$ the same count gives a hat point two ways to reach three points, which is one heuristic reason why the pattern stops at four hats; a SAT search confirms that no fifth hat can be added inside this family for $q=4,5,7,8,9,11,13$ (`research/plus2/REPORT.md`).

*Why the flags $(X_s,\lambda_s)$ are deleted.* The patches $X_a\mathrel{\mathrm{I}}M$ and $Q\mathrel{\mathrm{I}}\lambda_a$ raise the degrees of $X_a$ and $\lambda_a$, which were already $q+2$, to $q+3$; deleting the flag $(X_a,\lambda_a)$ brings both back to $q+2$. The rotation is degree-neutral: $X_t$ trades $\lambda_t$ for $\lambda_{\sigma(t)}$, and $\lambda_t$ trades $X_t$ for $X_{\sigma^{-1}(t)}$. Deleting a flag $(X,\lambda)$ from a projective plane makes exactly $q$ pairs of points non-collinear (the pairs $\{X,Y\}$, $Y$ a point of $\lambda$ other than $X$) and $q$ pairs of lines non-concurrent (the pairs $\{\lambda,N\}$, $N$ a line through $X$ other than $\lambda$). After the deletions and the rotation, the pairs of points of $\Pi$ that have no common line of $\Pi$ any more are:

- three hats: $\{X_a,Y\}$ for the $q$ points $Y\ne X_a$ of $\lambda_a$, and dually $\{\lambda_a,N\}$ for the $q$ lines $N\neq\lambda_a$ through $X_a$;

- four hats: $\{X_s,Y\}$ for $s\in S$ and the $q-1$ points $Y$ of $\lambda_s$ other than $A$ and $X_s$, and $\{X_a,A\}$; dually $\{\lambda_s,N\}$ for the $q-1$ lines $N$ through $X_s$ other than $\ell$ and $\lambda_s$, and $\{\lambda_a,\ell\}$. That is $4(q-1)+1$ pairs of each kind. The pairs $\{X_t,A\}$ and $\{\lambda_t,\ell\}$, $t\in T$, are not broken, because $X_t$ and $A$ are both on $\lambda_{\sigma(t)}$, and $\lambda_t$ and $\ell$ both contain $X_{\sigma^{-1}(t)}$.

Each broken pair is repaired by the crossing and one patch: $X_s$ and the points of $\lambda_s$ other than $A$ are all on $K_s$ (rule (R3)), and $A\mathrel{\mathrm{I}}K_a$ repairs $\{X_a,A\}$; dually $\lambda_s$ and the lines through $X_s$ other than $\ell$ all pass through $H_s$, and $H_a\mathrel{\mathrm{I}}\ell$ repairs $\{\lambda_a,\ell\}$. This is why the flags may be deleted at all: the crossing has already given every point of $\lambda_s$ a second line through $X_s$ (namely $K_s$), and every line through $X_s$ a second point on $\lambda_s$ (namely $H_s$).

Figure 2 shows the local picture at a hat pair; Table 3 shows the whole gadget.

*\[Figure: see SYNTHETIC.pdf.\]*

*Figure 2.* The local picture at a hat pair $(H_t,K_t)$, $t\in T$, of the four hats, in the incidence graph. Circles are points, squares are lines, new elements and new incidences are red, the dashed edge is the deleted flag $(X_t,\lambda_t)$. The upper blob is the set of $q-1$ lines through $X_t$ other than $\ell$ and $\lambda_t$, the lower blob the $q-1$ points of $\lambda_t$ other than $A$ and $X_t$. $H_t$ and $X_t$ are twins on the upper blob, $K_t$ and $\lambda_t$ twins on the lower blob, and the flag $(X_t,\lambda_t)$ is replaced by the crossed pair $X_t\mathrel{\mathrm{I}}K_t$, $H_t\mathrel{\mathrm{I}}\lambda_t$. Every element shown has degree $q+2$. For the three hats ($t\in\{0,1\}$) the dashed flag is kept, the edges to $\lambda_{\sigma(t)}$ and $X_{\sigma^{-1}(t)}$ are absent, and the links go to $K_{\pi(t)}$ and $H_{\pi(t)}$, $\pi=(0\ 1)$.

## 1.5 Degrees and counts

**Lemma 1.4.** In $\mathcal{S}$ every element has degree $q+1$ or $q+2$. The points of degree $q+1$ (the *deficient* points) are the points of $\Pi$ off $\ell$, other than $A$, on the lines joining $A$ to the unmarked points of $\ell$; dually, the lines of degree $q+1$ are the lines of $\Pi$ not through $A$, other than $\ell$, through the unmarked points of $\ell$. There are $(q-1)(q+1-|S|)$ of each: $(q-1)(q-2)$ for the three hats and $(q-1)(q-3)$ for the four hats. Each deficient point lies on exactly $q-|S|$ deficient lines, and each deficient line has exactly $q-|S|$ deficient points.

*Proof.* Count the lines through each point: those of $\Pi$, minus deleted flags, plus added ones. $A$: $q+1$ lines and $K_a$. An unmarked point of $\ell$: $q+1$ lines and $M$. $X_a$: loses $\lambda_a$, gains $M$ and $K_a$. $X_t$, $t\in T$: four hats, loses $\lambda_t$ and gains $\lambda_{\sigma(t)}$ and $K_t$; three hats, gains $K_t$. A point $p\notin\ell$, $p\neq A$: it is on exactly one line through $A$, the line $Ap$; it loses nothing, and gains $K_s$ exactly when $Ap=\lambda_s$. $Q$: $|\Lambda^*|+|S|=(q+1-|T|)+|S|=q+2$. $H_s$: $q$ lines by (R2), $M$, and one link line. The lines are the dual count (Lemma 1.6 below). A deficient point $p$ lies on $Ap$ and on $q$ lines meeting $\ell$ in the $q$ points other than $Ap\cap\ell$; among these, $q-|S|$ are unmarked. $\square$

So $\mathcal{S}$ has $q^2+q+1+|S|+1$ points and as many lines: $2(q^2+q+5)$ elements for the three hats and $2(q^2+q+6)$ for the four hats. To make it regular, join each deficient point to a deficient line not through it, by a perfect matching. Such a matching exists when there are deficient elements ($|S|\le q$; for the four hats with $q=3$ the structure is already regular): the bipartite graph of non-incident pairs between deficient points and deficient lines is regular of degree $(q-1)(q+1-|S|)-(q-|S|)>0$, and a regular bipartite graph of positive degree has a perfect matching (König). Adding flags cannot increase distances. (In $\mathrm{PG}(2,q)$ explicit matchings are given in coordinates in \[AL20\] and in `coords.tex`; any matching of non-incident pairs works.)

## 1.6 The diameter

**Lemma 1.5 (Points).** Any two distinct points of $\mathcal{S}$ are collinear in $\mathcal{S}$; Table 4 gives a common line for every pair.

| pair of points                                                                            | common line                                      | three hats          |
|:------------------------------------------------------------------------------------------|:-------------------------------------------------|:--------------------|
|                                                                                           |                                                  |                     |
| the line $uv$ of $\Pi$ keeps both incidences                                              | $uv$                                             |                     |
| $u=X_s$, $v$ a point of $\lambda_s$ other than $A$, $X_s$, flag $(X_s,\lambda_s)$ deleted | $K_s$                                            | only $s=a$          |
| $u=X_a$, $v=A$                                                                            | $K_a$                                            |                     |
| $u=X_t$, $v=A$, $t\in T$ (four hats)                                                      | $\lambda_{\sigma(t)}$                            | $\lambda_t$ is kept |
|                                                                                           |                                                  |                     |
| $u=A$                                                                                     | $\lambda_a$                                      |                     |
| $u=X_s$                                                                                   | $K_s$                                            |                     |
| $u$ an unmarked point of $\ell$                                                           | $Au$                                             |                     |
| $u\notin\ell$, $u\ne A$, $Au\in\Lambda^*$                                                 | $Au$                                             |                     |
| $u\notin\ell$, $u\ne A$, $Au=\lambda_t$ with $t\in T$                                     | $K_t$                                            |                     |
|                                                                                           |                                                  |                     |
| $u\notin\ell$ (including $u=A$)                                                           | $uX_s$                                           |                     |
| $u=X_s$                                                                                   | a line through $X_s$ other than $\ell,\lambda_s$ |                     |
| $u\in\ell^*$, $u\neq X_s$                                                                 | $M$                                              |                     |
| $s=a$, $u=X_t$ with $t\in T$                                                              | $\ell$                                           |                     |
| $s=t\in T$, $u=X_{\pi(t)}$                                                                | $K_{\pi(t)}$                                     | $\pi=(0\ 1)$        |
| $s=t\in T$, $u=X_{\sigma^{-1}(t)}$ (four hats)                                            | $\lambda_t$                                      | does not occur      |
|                                                                                           |                                                  |                     |
| $H_s$ and $H_{s'}$                                                                        | $M$                                              |                     |
| $Q$ and $H_a$                                                                             | $\lambda_a$                                      |                     |
| $Q$ and $H_t$, $t\in T$                                                                   | $K_{\pi(t)}$                                     |                     |

*Table 4.* A common line for every pair of distinct points of $\mathcal{S}$. Here $s,s'\in S$ and $t\in T$. The third column notes where the three hats differ; elsewhere the entry is the same for both constructions.

*Proof.* We check that Table 4 covers every pair and that each named line contains both points. The only flags of $\Pi$ missing from $\mathcal{S}$ are among the $(X_s,\lambda_s)$; so a flag $(u,L)$ of $\Pi$ survives whenever $u\notin\ell$ or $L$ does not pass through $A$.

*Two points of $\Pi$.* If the line $uv$ of $\Pi$ lost an incidence, then (up to order) $u=X_s$, $uv=\lambda_s$ with the flag deleted, and $v$ is $A$ or another point of $\lambda_s$. If $v\neq A$, both lie on $K_s$ by (R3). If $v=A$ and $s=a$: $X_a\mathrel{\mathrm{I}}K_a$ by (R3) and $A\mathrel{\mathrm{I}}K_a$ by (R6). If $v=A$ and $s=t\in T$ (four hats): the rotation puts $X_t$ on $\lambda_{\sigma(t)}$, which passes through $A$.

*$Q$ and a point $u$ of $\Pi$.* $\lambda_a\in\Lambda^*$ passes through $A$ and carries $Q$. $K_s$ contains $X_s$ and $Q$. An unmarked point $u$ of $\ell$: $Au\in\Lambda^*$, and the flag $(u,Au)$ was not touched. A point $u\notin\ell$, $u\ne A$: the flag $(u,Au)$ survives; if $Au\in\Lambda^*$ it carries $Q$; otherwise $Au=\lambda_t$, $t\in T$, and $u$ is a point of $\lambda_t$ other than $A$, so $u\mathrel{\mathrm{I}}K_t\ni Q$.

*$H_s$ and a point $u$ of $\Pi$.* If $u\notin\ell$, the line $uX_s$ of $\Pi$ is not $\ell$, so it carries $H_s$, and it contains $u$ in $\mathcal{S}$. If $u=X_s$, any of the $q-1\ge1$ lines through $X_s$ other than $\ell$ and $\lambda_s$ carries both. If $u\in\ell^*$ (this includes $X_a$ when $s\neq a$), use $M$. The remaining case is $u=X_{t'}$ with $t'\in T\setminus\{s\}$. If $s=a$, then $H_a\mathrel{\mathrm{I}}\ell$. If $s=t\in T$: for the three hats $t'=\pi(t)$; for the four hats $t'\in\{\sigma(t),\sigma^{-1}(t)\}$, as $\sigma$ is a $3$-cycle. The line $K_{\pi(t)}$ contains $X_{\pi(t)}$ by (R3) and $H_t$ by the link. The line $\lambda_t$ contains $X_{\sigma^{-1}(t)}$ by the rotation and $H_t$ by (R2).

*Two new points.* $M$ carries all hat points. $\lambda_a$ carries $Q$ (as $\lambda_a\in\Lambda^*$) and $H_a$ (as a line through $X_a$ other than $\ell$). $K_{\pi(t)}$ carries $Q$ and, by the link, $H_t$. $\square$

For lines we use duality. In the dual plane $\Pi^D$ the line $\ell$ is a point and $A$ a line not through it, the lines $\lambda_s$ are points on the line $A$, and the line joining the points $\ell$ and $\lambda_s$ is the point $X_s$.

**Lemma 1.6 (Duality).** The dual of $\mathcal{S}(\Pi;A,\ell,(X_s),\pi,\rho)$ is $\mathcal{S}(\Pi^D;\ell,A,(\lambda_s),\pi^{-1},\rho^{-1})$, by the identity on the elements of $\Pi$ and $H_s\leftrightarrow K_s$, $Q\leftrightarrow M$. Consequently any two distinct lines of $\mathcal{S}$ are concurrent.

*Proof.* Read the six rules in $\Pi^D$ with the frame $(\ell,A,(\lambda_s))$. Rule (R1) deletes the flags $(\lambda_s,X_s)$ and adds $\lambda_t\mathrel{\mathrm{I}}X_{\rho^{-1}(t)}$, which is the rotation $X_u\mathrel{\mathrm{I}}\lambda_{\rho(u)}$ of $\mathcal{S}$. Rule (R2) gives a new element incident with every element incident with $\lambda_s$ other than $A$: this is $K_s$; rule (R3) gives one incident with every element incident with $X_s$ other than $\ell$: this is $H_s$. Rule (R4) gives a new element incident with the lines through $A$ other than the $\lambda_t$, $t\in T$, and with all $K_s$: this is $Q$; likewise (R5) gives $M$. Rule (R6) gives $\ell\mathrel{\mathrm{I}}H_a$, $K_a\mathrel{\mathrm{I}}A$ and $K_t\mathrel{\mathrm{I}}H_{\pi^{-1}(t)}$, which are the links of $\mathcal{S}$. Since $\Pi^D$ is a projective plane of order $q$ and $\pi^{-1}$, $\rho^{-1}$ are again of the required kind (for the three hats $\pi^{-1}=\pi$, $\rho^{-1}=\rho$; for the four hats $\pi^{-1}=\rho^{-1}=\sigma^{-1}$, a $3$-cycle), Lemma 1.5 for the dual structure says that any two lines of $\mathcal{S}$ are concurrent. $\square$

**Theorem 1.7.** Let $\Pi$ be a projective plane of order $q\ge 3$. The three-hat structure of \[AL20\] and the four-hat structure are incidence structures with all degrees $q+1$ or $q+2$ and diameter $3$, with $2(q^2+q+5)$ and $2(q^2+q+6)$ elements. Adding a perfect matching of non-incident pairs between the deficient points and lines makes them $(q+2)$-regular. Hence $n_b(q+2,3)\ge 2(q^2+q+6)$ for every prime power $q\ge 3$.

*Proof.* Degrees and counts are Lemma 1.4. Every element is incident with something. By Lemmas 1.5 and 1.6 any two points are collinear and any two lines concurrent, so by Lemma 0.1(a) the diameter is at most $3$; it is $3$ because $A\mathrel{\not\mathrel{\mathrm{I}}}\ell$. $\square$

Only the axioms of a projective plane are used, so the theorem holds in non-Desarguesian planes too (we checked the nearfield plane of order $9$). In the range of the tables, $q=9,11,13$ give $192$, $276$, $376$ at $\Delta=11,13,15$, two more than \[AL20\].

## 1.7 From three hats to four, step by step

Start from the three hats with labels $0,1,a$ and choose a fourth point $X_c$ of $\ell$, different from $X_0,X_1,X_a$. The four-hat structure arises by exactly these changes:

(1) add the point $H_c$, on the $q$ lines through $X_c$ other than $\ell$, on $M$ and on $K_1$; add the line $K_c$, through the $q$ points of $\lambda_c$ other than $A$, through $Q$ and through $H_0$;

(2) delete the flags $(X_0,\lambda_0)$, $(X_c,\lambda_c)$, $(X_1,\lambda_1)$, and add $(X_0,\lambda_c)$, $(X_c,\lambda_1)$, $(X_1,\lambda_0)$;

(3) delete $X_c\mathrel{\mathrm{I}}M$ and $Q\mathrel{\mathrm{I}}\lambda_c$ (now $X_c$ is a $T$-point and $\lambda_c$ a $T$-line);

(4) delete the link $H_0\mathrel{\mathrm{I}}K_1$; it is replaced by $H_0\mathrel{\mathrm{I}}K_c$ and $H_c\mathrel{\mathrm{I}}K_1$ from (1), while $H_1\mathrel{\mathrm{I}}K_0$ is kept.

In terms of the links, the cycle $0\to1\to0$ of $\pi=(0\ 1)$ becomes the cycle $0\to c\to 1\to 0$ of $\sigma$. The four-hat structure has $2q+1$ more flags than the three-hat structure: $2(q+2)$ at $H_c$ and $K_c$, three from the rotation, minus six. (Checked by computer against the coordinate versions for $q=4,5,7$ and every choice of $a,c$.)

# 2. Diameter 4: clones and shadow lines in generalized quadrangles

A *generalized quadrangle* of order $(s,t)$ is an incidence structure in which every line has $s+1$ points, every point is on $t+1$ lines, and

<div class="center">

for every anti-flag $(p,L)$ there is *exactly one* point of $L$ collinear with $p$.

</div>

It has $(s+1)(st+1)$ points and $(t+1)(st+1)$ lines, and its incidence graph has diameter $4$ and girth $8$. By Lemma 0.1(b), an incidence structure has diameter at most $4$ as soon as for every anti-flag $(p,L)$ there is *at least one* point of $L$ collinear with $p$. All constructions in this section only add points, lines and incidences to a quadrangle; nothing is deleted or moved, so no pair of points stops being collinear.

This is the first difference with diameter $3$. In a projective plane two cloned points (new points on all lines through an old point) would overload the line joining them, and the hats of Section 1 are clones of the points $X_s$ that avoid the common line $\ell$. In a quadrangle, a clone of a point inherits the covering property from its point at once; what has to be arranged is only that every line receives the same number of clones, and this is what an $m$-ovoid is.

## 2.1 Clones and shadow lines

Let $\mathcal{S}$ be a generalized quadrangle of order $(s,t)$.

- A *clone* of a point $p$ is a new point incident with exactly the lines of $\mathcal{S}$ through $p$.

- A *shadow line* over a line $L$ is a new line that contains, for each point $p$ of $L$, exactly one point *over* $p$: either $p$ itself or one of the clones of $p$, called the *stand-in* for $p$.

**Definition 2.1 (Theorem B of the lab).** Let $w$ assign to every point $p$ a number $w(p)\ge 0$, and let $\mathcal{M}$ be a finite list of lines of $\mathcal{S}$ (repetitions allowed). The structure $\mathcal{S}[w,\mathcal{M}]$ has the points and lines of $\mathcal{S}$, $w(p)$ clones of each point $p$, and one shadow line over each entry of $\mathcal{M}$, with a chosen stand-in for each of its points. Its incidences are those of $\mathcal{S}$, those of the clones, and those of the shadow lines with their points.

*\[Figure: see SYNTHETIC.pdf.\]*

*Figure 3.* Left: a point $p$ with two clones $p',p''$; all three are on the $t+1$ lines through $p$ and on no other line of $\mathcal{S}$. Right: a shadow line $L^\mu$ over $L$; for the point $x$ of $L$ the stand-in is a clone of $x$, for the other points of $L$ it is the point itself. The clone of $x$ is on $L$ as well, being on every line through $x$.

*What happens to the combinatorics.* No incidence is deleted, so every pair of old points that was collinear stays collinear. A point $p$ and its clones are pairwise collinear, on $t+1$ common lines; two lines through $p$ now meet in $1+w(p)$ points; a shadow line whose stand-ins are all original has the same points as its line. So the structure is no longer a partial linear space, but these coincidences are harmless. Two old points that were not collinear stay non-collinear: they have no common old line, a shadow line over $L$ contains only points over points of $L$, and an old point is over itself only.

*Why the diameter is $4$.* Write $\bar x$ for the old point under a point $x$ ($\bar x=x$ for an old point, $\bar x=p$ for a clone of $p$) and $\bar Y$ for the old line under a line $Y$. Every point $x$ is on every old line through $\bar x$. Let $(x,Y)$ be an anti-flag.

- $Y$ old. Then $\bar x\mathrel{\not\mathrel{\mathrm{I}}}Y$; let $r$ be the point of $Y$ collinear with $\bar x$, on the line $N$. Then $x\mathrel{\mathrm{I}}N\mathrel{\mathrm{I}}r\mathrel{\mathrm{I}}Y$.

- $Y$ a shadow line, $\bar x\mathrel{\not\mathrel{\mathrm{I}}}\bar Y$. Let $r$ be the point of $\bar Y$ collinear with $\bar x$, on the line $N$, and $r^*$ the stand-in for $r$ on $Y$. Then $x\mathrel{\mathrm{I}}N\mathrel{\mathrm{I}}r^*\mathrel{\mathrm{I}}Y$, as $r^*$ is on every old line through $r$.

- $Y$ a shadow line, $\bar x\mathrel{\mathrm{I}}\bar Y$. Take a point $r\ne\bar x$ of $\bar Y$ and its stand-in $r^*$: then $x\mathrel{\mathrm{I}}\bar Y\mathrel{\mathrm{I}}r^*\mathrel{\mathrm{I}}Y$.

So in every case some point of $Y$ is collinear with $x$, and the diameter is at most $4$ (Lemma 0.1(b)); it is $4$ because non-collinear old points remain.

*Degrees.* An old line $L$ has $s+1+\sum_{p\mathrel{\mathrm{I}}L}w(p)$ points. A shadow line has $s+1$ points. An old point or a clone is on $t+1$ old lines plus the shadow lines for which it is the stand-in. This proves:

**Theorem 2.2 (Theorem B).** For every generalized quadrangle $\mathcal{S}$ of order $(s,t)$, every $w$, $\mathcal{M}$ and choice of stand-ins, $\mathcal{S}[w,\mathcal{M}]$ has diameter $4$, $(s+1)(st+1)+\sum_pw(p)$ points and $(t+1)(st+1)+|\mathcal{M}|$ lines. Its maximum degree is at most $\Delta$ if and only if $\Delta\ge\max(s,t)+1$, every line of $\mathcal{S}$ carries clones of total number at most $\Delta-s-1$, and every point (old or clone) is the stand-in for at most $\Delta-t-1$ entries of $\mathcal{M}$.

## 2.2 Exact weights: $m$-ovoids and covers

A *weighted $m$-ovoid* is a weight $w$ on the points such that every line carries total weight exactly $m$; equivalently, a multiset of points meeting every line in exactly $m$ points, counted with multiplicity. It is an *$m$-ovoid* if it is a set, and an *ovoid* if moreover $m=1$ (a set of points meeting every line once). Dually, a *weighted $m$-cover* is a multiset of lines with exactly $m$ members through every point, and a *spread* is a set of lines partitioning the points.

**Corollary 2.3.** Let $\Delta\ge\max(s,t)+1$, let $w$ be a weighted $(\Delta-s-1)$-ovoid and $\mathcal{M}$ a weighted $(\Delta-t-1)$-cover, with every stand-in original. Then every old element of $\mathcal{S}[w,\mathcal{M}]$ has degree exactly $\Delta$, every clone $t+1$ and every shadow line $s+1$, and there are $2\Delta(st+1)$ elements in all. Joining the clones to the shadow lines by a suitable set of anti-flags makes the structure $\Delta$-regular, with diameter still $4$.

(Counting flags gives $\sum_pw(p)=(\Delta-s-1)(st+1)$ and $|\mathcal{M}|=(\Delta-t-1)(st+1)$. No clone is on a shadow line, so all clone–shadow pairs are anti-flags, and the missing incidences can be added in any balanced way, for instance cyclically; `POLISHED.md`, Corollary 3.3.)

So for diameter $4$ the whole question is: *which quadrangles carry weighted $m$-ovoids and covers for the right $m$?* Three answers give the lab’s values.

## 2.3 Theorem A: two elliptic quadrics in the Ahrens–Szekeres quadrangle

Let $q$ be odd and $\Delta=q+2$. The quadrangle is $\mathrm{AS}(q)$, of order $(q-1,q+1)$; then $\Delta-s-1=2$ and $\Delta-t-1=0$, so we need a *weighted $2$-ovoid of $\mathrm{AS}(q)$ and no shadow lines*. Every point of $\mathrm{AS}(q)$ is already on $t+1=q+2$ lines, so the clones have full degree and the result is $(q+2)$-regular.

*The quadrangle.* $\mathrm{AS}(q)$ is Payne’s derived quadrangle of the symplectic quadrangle $W(q)$ at a point $x$ \[P71, PT\], and its definition is combinatorial. For points $u,v$ write $\{u,v\}^\perp$ for the set of points collinear with both, and $\{u,v\}^{\perp\perp}$ for the set of points collinear with every point of $\{u,v\}^\perp$; in $W(q)$, for $u,v$ not collinear, $\{u,v\}^{\perp\perp}$ has $q+1$ points (every point of $W(q)$ is regular). Then:

- the points of $\mathrm{AS}(q)$ are the $q^3$ points of $W(q)$ not collinear with $x$ (and different from $x$);

- its lines are (i) the lines of $W(q)$ not through $x$, each without its unique point collinear with $x$, and (ii) the sets $\{x,y\}^{\perp\perp}\setminus\{x\}$, $y$ not collinear with $x$ (the *hyperbolic lines*).

Every line has $q$ points, every point is on $q+2$ lines, and the $q^2$ hyperbolic lines form a spread of $\mathrm{AS}(q)$.

*The configuration used.* Two sets $\mathcal{E}_1,\mathcal{E}_2$ of $q^2$ points of $\mathrm{AS}(q)$ such that

(E1) each hyperbolic line meets $\mathcal{E}_1$ in exactly one point and $\mathcal{E}_2$ in exactly one point;

(E2) every other line of $\mathrm{AS}(q)$ meets $\mathcal{E}_1$ and $\mathcal{E}_2$ in exactly two points in total (a point of $\mathcal{E}_1\cap\mathcal{E}_2$ counted twice).

Then $w=\mathbf 1_{\mathcal{E}_1}+\mathbf 1_{\mathcal{E}_2}$ is a weighted $2$-ovoid. Such a pair exists for every odd $q$: two elliptic quadrics of $\mathrm{PG}(3,q)$ through $x$, both tangent to the plane of points collinear with $x$, in a suitable relative position; they meet in $x$ and in one point $e$ of $\mathrm{AS}(q)$ (`POLISHED.md`, Theorem 4.1; the proof is a discriminant computation, and a line of type (i) meets the two quadrics in $1+\chi$ and $1-\chi$ points for some $\chi\in\{-1,0,1\}$). So:

<div class="center">

*Clone every point of $\mathcal{E}_1$ and every point of $\mathcal{E}_2$ once* (so $e$ gets two clones).

</div>

Each line of $\mathrm{AS}(q)$ gains exactly two clones, each clone is on the $q+2$ lines of its point, nothing else changes, and Theorem 2.2 gives a $(q+2)$-regular structure of diameter $4$ with $q^3+q^2(q+2)+2q^2=2q^2(q+2)$ elements. At $q=9,11,13$: $1782$, $3146$, $5070$. Weights are needed: $\mathrm{AS}(3)$ has no $2$-ovoid and $\mathrm{AS}(5)$ no $m$-ovoid for $m\le4$ (integer programs, `POLISHED.md` §4). And nothing more can be added at $\Delta=q+2$: points are full, and every line has room for exactly two clones.

## 2.4 Proposition C: a $2$-ovoid and a spread of $W(q)$

Let $q$ be odd and $\Delta=q+3$ in $W(q)$, of order $(q,q)$; now $\Delta-s-1=\Delta-t-1=2$. The configuration used is a *$2$-ovoid* $\mathcal{O}$ of $W(q)$ (a set of $2(q^2+1)$ points meeting every line in exactly two points) and a *spread* $\Sigma$ ($q^2+1$ lines partitioning the points). The construction:

<div class="center">

*Clone every point of $\mathcal{O}$ once, and put two shadow lines over every line of $\Sigma$.*

</div>

Every old line gains two clones, every old point is on two shadow lines (those over its spread line), clones and shadow lines have degree $q+1$, and Corollary 2.3 completes it to a $(q+3)$-regular structure of diameter $4$ with $2(q^2+1)(q+3)$ elements; one explicit completion joins the $i$-th clone to the shadow lines $2i$ and $2i+1$ (indices modulo $2(q^2+1)$, in any numbering). At $q=13$ this is $5440$ at $\Delta=16$. $2$-ovoids of $W(q)$, $q$ odd, exist: the union of two suitable classes of Ebert’s partition of $\mathrm{PG}(3,q)$ into elliptic quadrics (orbits of a Singer subgroup) is one (`POLISHED.md`, Proposition 5.1); see also \[BLP09\]. Spreads of $W(q)$ exist for every $q$.

## 2.5 Even $q$, and all degrees

For even $q$, $W(q)$ has both an ovoid $\mathcal{O}$ and a spread $\Sigma$ \[PT\]. With $j$ clones of every point of $\mathcal{O}$ and $j$ shadow lines over every line of $\Sigma$, Corollary 2.3 gives a $(q+1+j)$-regular structure of diameter $4$ with $2(q+1+j)(q^2+1)$ elements. Combining the three cases (ovoid and spread for even $q$; $j/2$ copies of a $2$-ovoid and $j$ copies of a spread for odd $q$ and even $j$; $\mathrm{AS}(q)$ with $(\Delta-q)/2$ copies of the weighted $2$-ovoid of Theorem A and $\Delta-q-2$ copies of the hyperbolic spread for odd $q$ and odd $j$) gives $n_b(\Delta,4)\ge 2q^2\Delta$ for every prime power $q\le\Delta-1$ (`POLISHED.md`, Corollary 5.3).

## 2.6 For comparison: Delorme’s doubling, and stand-ins

*Delorme’s construction* behind the 2013 values \[D85a\] takes a spread $\Sigma$ of $W(q)$ and a line $v\in\Sigma$. Each line of $\Sigma$ other than $v$ gets one copy with the same points (a shadow line with all stand-ins original); each point of $v$ gets one copy, which is on the $q$ lines through the point other than $v$; and $v$ gets three copies, one through the original points of $v$ and two through the copies. All degrees are at most $q+2$, the diameter is $4$, and there are $2(q+1)(q^2+1)+q^2+q+4$ elements. It is a doubling in Delorme’s sense: the copied set is the spread with the points of one of its lines, at two levels. Theorem 2.2 is not a doubling: since a clone is on *every* old line through its point, no condition on the shape of the copied set is needed, and whole $m$-ovoids can be cloned.

*Stand-ins: the $(7,4)$ example.* In the quadrangle $Q(4,5)$ (order $(5,5)$) take an ovoid $\mathcal{O}$ and clone each of its $26$ points once: every line gains one clone and has degree $7$, every old point has degree $6$. Shadow lines can now be added as long as every point serves at most one of them: a point off $\mathcal{O}$ has no clone and can be on at most one shadow line, while a point of $\mathcal{O}$ can be on two, standing in for itself on one and letting its clone stand in on the other. An integer program finds $21$ such shadow lines (four points of $\mathcal{O}$ are on two of them), giving $2\cdot6\cdot26+26+21=359$ elements, maximum degree $7$ and diameter $4$ (`POLISHED.md`, Appendix A). In this family at most $q^2-q+2$ shadow lines are possible (`POLISHED.md`, Remark 3.5).

# 3. Diameter 6: a spread and whiskers in a generalized hexagon

Let $\Gamma$ be a generalized hexagon of order $(q,q)$: every line has $q+1$ points, every point is on $q+1$ lines, any two elements are at distance at most $6$ in the incidence graph, and there are no circuits of length less than $12$. It has $N=(q+1)(q^4+q^2+1)$ points and $N$ lines. Elements at distance $6$ are *opposite*; two elements at distance less than $6$ are joined by a unique shortest path. A point and a line are at distance $1$, $3$ or $5$. In the constructions, $\Gamma$ is the split Cayley hexagon $H(q)$ \[T59, VM98\], but only in the choice of the special configurations (§3.2).

By Lemma 0.1(c) the diameter stays at most $6$ if for every anti-flag $(p,L)$ some point of $L$ is within distance $4$ of $p$. Here the new elements come from a doubling, and the argument is by “sheets”.

## 3.1 Doubling with levels

This is Delorme’s operation \[D85a, §7\], in incidence language. Choose sets of elements (points and lines mixed) $$\mathcal{A}_0\supseteq\mathcal{A}_1\supseteq\mathcal{A}_2\supseteq\cdots,$$ and call $\max\{k: x\in\mathcal{A}_k\}$ the *level* of $x$ (level $-1$ if $x\notin\mathcal{A}_0$). Fix $m\ge2$.

**Definition 3.1 (Doubling with levels).** Replace every element $x$ of level $k$ by $m^{k+1}$ *versions* $x^w$, one for each word $w$ of length $k+1$ over $\{1,\dots,m\}$; an element of level $-1$ keeps one version, itself. Declare $x^w\mathrel{\mathrm{I}}y^u$ if and only if $x\mathrel{\mathrm{I}}y$ in $\Gamma$ and one of the words $w,u$ is a prefix of the other.

For $m=2$ and a single level this says: every element $x$ of $\mathcal{A}_0$ gets a twin $x'$; inside $\mathcal{A}_0$ originals see originals and twins see twins; an element outside $\mathcal{A}_0$ sees both $x$ and $x'$ whenever it saw $x$. So an outside element gains one incidence for each element of $\mathcal{A}_0$ it is incident with, and an element of $\mathcal{A}_0$ gains nothing. With more levels, a version $x^w$ of level $k$ sees one version of each neighbour of level at most $k$ (the one whose word is the corresponding prefix of $w$) and all $m$ versions of a neighbour of level $k+1$ extending $w$.

*Sheets.* For an infinite word $\omega$, the versions whose words are prefixes of $\omega$ form a copy of $\Gamma$ (every element has exactly one version in it, and any two of these versions have comparable words). Two sheets share exactly the versions indexed by their common prefixes: all elements of level $-1$, then the versions of level-$0$ elements if the words begin with the same letter, and so on (Figure 4). So the doubled structure is $m^{r+1}$ copies of $\Gamma$ glued along a tree.

*\[Figure: see SYNTHETIC.pdf.\]*

*Figure 4.* Doubling with three levels, $m=2$. An element of level $k$ has one version for each node at depth $k+1$; versions are incident when their elements are and their nodes lie on a common path from the root. Each leaf (an infinite word, here of length $3$) is a sheet, a copy of $\Gamma$ consisting of the versions on the path from the root to that leaf. Elements of level $-1$ are shared by all eight sheets.

Two conditions control the degrees and one the diameter:

(L0) every element outside $\mathcal{A}_0$ is incident with at most one element of $\mathcal{A}_0$;

(L1) for every $i\ge0$, every element incident with an element of $\mathcal{A}_{i+1}$ lies in $\mathcal{A}_i$, and every element of $\mathcal{A}_i\setminus\mathcal{A}_{i+1}$ is incident with at most one element of $\mathcal{A}_{i+1}$;

(C) any two elements $x,y$ in one connected component of $\mathcal{A}_0$ (possibly $x=y$) admit an element $z\notin\mathcal{A}_0$ with $d(x,z)+d(z,y)\le 6$.

Under (L0) and (L1) every version has degree at most $q+1+(m-1)$: it sees one version of each neighbour, except of the one neighbour (if any) one level up, of which it sees $m$. Under (C) the diameter stays at most $6$: two versions in a common sheet are within $6$; two versions in no common sheet have incomparable words, so both elements are in $\mathcal{A}_0$; if they lie in different components of $\mathcal{A}_0$, a shortest path between them in $\Gamma$ passes through an element of level $-1$, which belongs to every sheet, and the two halves of the path can be lifted into the two sheets; if they lie in the same component, (C) gives such an element. In a generalized hexagon, (C) holds if and only if every connected component of $\mathcal{A}_0$ is a tree of diameter at most $4$ (the hat lemma, `POLISHED.md` Lemma 1.3: a path of length $5$ inside $\mathcal{A}_0$ is the unique shortest path between its ends, so no detour through an outside element is short enough). Finally there are $(m-1)\sum_k m^k|\mathcal{A}_k|$ new elements.

Counting flags between $\mathcal{A}_0$ and its complement gives a ceiling: if every component of $\mathcal{A}_0$ is a tree and $c$ is the number of components, then $q|\mathcal{A}_0|+2c\le 2N$, with equality exactly when every element outside $\mathcal{A}_0$ is incident with exactly one element of $\mathcal{A}_0$ (`geometry.tex`, Proposition 3.6).

## 3.2 The configuration: a spread, its distinguished line, and whiskers

*A spread* of $\Gamma$ is a set $S$ of $q^3+1$ pairwise opposite lines. We use two properties: the lines of $S$ have disjoint point sets, so every point of the set $\Pi$ of points on lines of $S$ is on exactly one line of $S$ ($|\Pi|=(q+1)(q^3+1)$); and every line not in $S$ meets exactly one line of $S$ (a line meeting two lines of $S$ would put them at distance $4$, and counting gives all $N$ lines). $H(q)$ has spreads for every $q$: the *Hermitian spreads*, the lines of $H(q)$ in a hyperplane that meets the quadric of $H(q)$ in an elliptic quadric \[T80\].

Fix a line $v\in S$. The points split by their distance from $v$: the $q+1$ points of $v$ (distance $1$), the $q^2(q+1)$ further points on the $q(q+1)$ lines meeting $v$ (distance $3$), and the rest (distance $5$). A point of $\Pi$ not on $v$ is at distance $5$ from $v$, because its line in $S$ is opposite $v$. Call a point *free* if it is not in $\Pi$ and is at distance $5$ from $v$; there are $$N-(q+1)-q^2(q+1)-q^3(q+1)=q^3(q^2-1)$$ free points.

*Whiskers.* Let $h$ be a line opposite $v$ and not in $S$. It meets exactly one line $n$ of $S$, with $n\ne v$, in one point; its other $q$ points are free (they are not in $\Pi$, since $h$ meets only one line of $S$ and only once, and every point of a line opposite $v$ is at distance $5$ from $v$). Such a line is a *whisker*, hanging from the point $h\cap n$.

**Definition 3.2.** A *whisker set* is a set $W$ of whiskers such that no free point is on two lines of $W$. It is *exact* if every free point is on exactly one line of $W$; then $|W|=q^3(q^2-1)/q=q^2(q^2-1)$, the largest possible.

Exact whisker sets exist in $H(q)$ for every $q$: for odd $q$ an explicit one is cut out by a family of $q^2$ Hermitian spreads through $v$, pairwise meeting only in $v$, with one whisker per free point chosen by an affine condition (`POLISHED.md`, Theorem 6.5); for even $q\ge4$ a characteristic-$2$ variant (Theorem 6.14); for $q=2$ one found by computer.

## 3.3 The levels, and what each element becomes

Put $$\mathcal{A}_2=\{v\},\qquad \mathcal{A}_1=\{v\}\cup\{\text{points of }v\}\cup S,\qquad \mathcal{A}_0=\mathcal{A}_1\cup\Pi\cup\{\text{lines meeting }v\}\cup W .$$ In words: $v$ is at level $2$; the other spread lines and the points of $v$ at level $1$; the other points of $\Pi$, the $q(q+1)$ lines meeting $v$ and the whiskers at level $0$; everything else at level $-1$.

*The conditions.* (L1): the elements incident with $v$ are its points, which are at level $1$, and each sees only $v$ at level $2$; the elements incident with a level-$1$ element are the points of $\Pi$ and the lines meeting $v$, all in $\mathcal{A}_0$, and each of them sees exactly one level-$1$ element (its spread line, or its point on $v$), while a whisker sees none. (L0) holds, and with $W$ exact it holds with equality: a point at distance $3$ from $v$ is on exactly one line meeting $v$ (two would close a circuit of length at most $6$) and on no whisker; a free point is on exactly one whisker; a line outside $\mathcal{A}_0$ meets exactly one line of $S$, hence contains exactly one point of $\Pi$, and no other element of $\mathcal{A}_0$. (C): the connected components of $\mathcal{A}_0$ are

- the *ball* of radius $2$ about $v$: the line $v$, its $q+1$ points and the $q(q+1)$ lines through them;

- for each of the $q^3$ lines $n\in S\setminus\{v\}$, the *broom* of $n$: the line $n$, its $q+1$ points, and the whiskers hanging from them.

Both are trees of diameter $4$ (Figure 5). Since $W$ is exact, the ceiling $q|\mathcal{A}_0|+2(q^3+1)=2N$ is attained: no family of this kind can double more.

*\[Figure: see SYNTHETIC.pdf.\]*

*Figure 5.* The two kinds of connected components of $\mathcal{A}_0$ (squares are lines, circles points; only some of the $q+1$ points and $q$ lines are drawn). Each is a tree of diameter $4$. The short grey strokes on a whisker stand for its $q$ free points, which are at level $-1$. Every element outside $\mathcal{A}_0$ is incident with exactly one element of $\mathcal{A}_0$, so the components together with their neighbours partition the elements of $\Gamma$.

*Every new element.* Write $i,j,k$ for letters in $\{1,\dots,m\}$. The versions and their neighbours are (`POLISHED.md`, §6.2):

<div class="center">

| element (level)                           | a version is incident with                                                                                     | degree |
|:------------------------------------------|:---------------------------------------------------------------------------------------------------------------|:-------|
| $v$ (2): $v^{ijk}$                        | $p^{ij}$ for the $q+1$ points $p$ of $v$                                                                       | $q+1$  |
| point $p$ of $v$ (1): $p^{ij}$            | $v^{ij1},\dots,v^{ijm}$; $L^i$ for the $q$ lines $L\ne v$ through $p$                                          | $q+m$  |
| line $n\in S\setminus\{v\}$ (1): $n^{ij}$ | $p^i$ for the $q+1$ points $p$ of $n$                                                                          | $q+1$  |
| point $p\in\Pi$ not on $v$ (0): $p^i$     | $n^{i1},\dots,n^{im}$ for its spread line $n$; $h^i$ for each whisker $h$ on $p$; every other line through $p$ | $q+m$  |
| line $L\ne v$ meeting $v$ (0): $L^i$      | $p^{i1},\dots,p^{im}$ for $p=L\cap v$; the $q$ other points of $L$                                             | $q+m$  |
| whisker $h$ (0): $h^i$                    | $p^i$ for the point $p$ of $h$ in $\Pi$; the $q$ free points of $h$                                            | $q+1$  |
| point $r\notin\Pi$ ($-1$)                 | all $m$ versions of the line through $r$ meeting $v$ or of its whisker; every other line through $r$           | $q+m$  |
| line $N\notin\mathcal{A}_0$ ($-1$)        | all $m$ versions of its point in $\Pi$; its $q$ other points                                                   | $q+m$  |

</div>

Nothing is deleted: every flag of $\Gamma$ survives in every sheet. The elements of level $-1$ see more (all versions of their one neighbour in $\mathcal{A}_0$), the versions of the spread lines and of the whiskers see less (only versions of their points), and these last are the elements of degree $q+1$.

**Theorem 3.3 (Theorem D).** With an exact whisker set, the doubling of $H(q)$ with these levels has maximum degree $q+m$, diameter $6$ and $$2N+(m-1)\bigl(2q^4+2q^3+2q+2+m(q^3+q+2)+m^2\bigr)$$ elements; for $m=2$ this is $2N+2q^4+4q^3+4q+10$.

At $q=5,9,11,13$ and $m=2$ this gives $9592$, $148944$, $388972$, $870440$, and at $q=13$, $m=3$ it gives $940846$. With $W=\emptyset$ the same levels are Delorme’s construction \[D85a, §8(b)\], which gives the 2013 values; the whiskers add $(m-1)q^2(q^2-1)$.

## 3.4 Theorem R: a regular version

The doubled structure has more lines than points, $(m-1)m(q^3-q+m)$ more, and its deficient elements are the versions of spread lines and whiskers. Two observations make it regular.

- *Repeated lines.* For $n\in S\setminus\{v\}$ and a letter $i$, the $m$ versions $n^{i1},\dots,n^{im}$ have the same points (the $p^i$, $p$ on $n$); likewise the versions $v^{ij1},\dots,v^{ijm}$. Deleting a line that has a twin with the same points changes no distance between the remaining elements (a shortest path through it may use the twin). Delete $(m-1)m(q^3-q+m)$ such lines, at most $m-1$ from each class of $m$, so that points and lines are equal in number.

- *Completion.* Now every element has degree between $q+1$ and $q+m$, and the deficits on the two sides have the same sum; this sum is large compared with $q+m$, and a swapping argument (`POLISHED.md`, Lemma 7.2) gives a set of anti-flags, one for each missing incidence, whose addition makes the structure $(q+m)$-regular. Adding flags does not increase distances.

The result has $2(q+1)\bigl(q^4+q^2+1+(m-1)(q^3+m+1)\bigr)$ elements: $9348$, $147500$, $386328$, $866068$ at $q=5,9,11,13$, $m=2$, and $927724$ at $q=13$, $m=3$. The completing anti-flags are not given by a rule; only their existence is proved.

# 4. Diameter 7: copies of a hexagon joined by matchings, freed sets and hubs

Let $\Gamma$ be a generalized hexagon of order $(q,q)$ with $N$ points and $N$ lines, as in Section 3, and $\Gamma^D$ its dual (points and lines exchanged). Two facts are used repeatedly: a point and a line of $\Gamma$ are at distance at most $5$, two elements of the same kind at most $6$; and for any two elements $x,y$ there is an element $z$ at distance $2$ from $x$ (a point collinear with $x$ if $x$ is a point, a line concurrent with $x$ if $x$ is a line) with $d(z,y)\le 3$ if $x,y$ are of different kinds and $d(z,y)\le 4$ if they are of the same kind (walk two steps from $x$ along a shortest path to $y$; if $x$ and $y$ are incident, take for $z$ another element incident with $y$; if $x=y$, any $z$).

## 4.1 Level structures

Fix $r\ge1$ and take $2r+1$ copies $\Gamma_0,\dots,\Gamma_{2r}$ of $\Gamma$, indexed modulo $2r+1$. For each copy $j$ and each $k=1,\dots,r$ (a *transition* from copy $j$ to copy $j+k$) choose a bijection $M_{j,k}$ from the points of $\Gamma_j$ to the lines of $\Gamma_{j+k}$.

**Definition 4.1 (Level structure).** Its points are the points of all copies, its lines the lines of all copies, and its incidences are those inside each copy together with $$p\mathrel{\mathrm{I}}M_{j,k}(p)\qquad\text{for every point $p$ of $\Gamma_j$ and every $k=1,\dots,r$.}$$

So every point gains $r$ lines, one in each of the next $r$ copies, and every line gains $r$ points, one from each of the previous $r$ copies: the structure is $(q+1+r)$-regular with $(2r+1)\cdot 2N$ elements. (Their orders are the 2013 table values at diameter $7$, which the CombinatoricsWiki table credits to Delorme, Gómez and Quisquater.) A copy may also be a copy of the dual $\Gamma^D$; its “points” are then lines of $\Gamma$. A transition from a copy of $\Gamma$ to a copy of $\Gamma^D$ is called *friendly*: it may join each point $p$ of $\Gamma$ to $p$ itself, now a line of the dual copy.

**Theorem 4.2 (Theorem A of `D7_HEXAGON.md`).** For any choice of the bijections, the level structure has diameter at most $7$.

*Proof.* Two elements of one copy are within $6$. Any two copies differ by $\pm k$ with $1\le k\le r$, since there are $2r+1$ of them; so take $u$ in copy $j$, $v$ in copy $j+k$, and $M=M_{j,k}$. If $u$ is a point: $u$, then $M(u)$, then $v$ inside copy $j+k$: at most $1+6$. If $u$ and $v$ are lines: $u$ to the point $M^{-1}(v)$ inside copy $j$, then $v$: at most $5+1$. If $u$ is a line and $v$ a point: choose a line $b$ through $v$; $u$ to the point $M^{-1}(b)$, then $b$, then $v$: at most $5+1+1$. $\square$

## 4.2 Freeing incidences and adding hubs

To add elements, incidences must be freed. For each transition $t=(j,k)$ choose a set $R_t$ of points of copy $j$, the *freed* points, and:

(1) delete the incidences $p\mathrel{\mathrm{I}}M_t(p)$, $p\in R_t$; each deletion leaves a free incidence (a *slot*) at the point $p$ of copy $j$ and one at the line $M_t(p)$ of copy $j+k$;

(2) add new lines, the *line-hubs*, each incident with one freed point in *every* copy (taking a slot there), and new points, the *point-hubs*, each incident with one freed line in every copy;

(3) add incidences between line-hubs and point-hubs (a *hub graph*), at most $q-r$ at each hub.

All degrees stay at most $q+1+r$ (a hub has $2r+1$ incidences with the copies), and there are $(2r+1)\cdot2N$ elements plus the hubs. Figure 6 shows the case $r=1$.

*\[Figure: see SYNTHETIC.pdf.\]*

*Figure 6.* Three copies ($r=1$) joined by matchings $M$ from the points of one copy to the lines of the next. Freeing the point $x$ on the transition $0\to1$ deletes the incidence of $x\in\Gamma_0$ with the line $M(x)\in\Gamma_1$ (dashed). In the records with $r=1$ every transition frees the same set $R$, and the line-hub $h_x$ takes the slot of the copy of $x$ in each of the three copies; a point-hub $g_x$ (not drawn) takes the slots of the three copies of the line $M(x)$.

*What the hubs need.* A line-hub is incident with a point in every copy, which is within $6$ of everything in its copy: so a hub is within $7$ of every element of every copy. A line-hub and a point-hub are within $7$ through copy $0$ (a point and a line of one copy are within $5$). Two hubs of the same kind must be within $6$, through the hub graph or through the copies. *What the deletion breaks.* Only pairs in two copies joined by a transition can be affected, and only through that transition. Call a transition *repaired* if after the deletion every element of copy $j$ is still within $7$ of every element of copy $j+k$ using only these two copies and the remaining incidences of the transition. Then:

**Theorem 4.3 (Assembly, `D7_HEXAGON.md` Theorem 3.4).** If every transition is repaired and any two hubs of the same kind are within distance $6$, the structure has diameter at most $7$.

So everything reduces to a property of one matching and one freed set, and to finding a hub graph. Two answers to the first question:

## 4.3 Matchings that extend to an isomorphism: segment sets

Suppose the transition’s bijection is the restriction of an isomorphism $\psi$ from copy $j$ to copy $j+k$ that sends points to lines: the identity of a friendly transition, or a *duality* of $\Gamma$ (an incidence-preserving bijection exchanging points and lines; $H(q)$ has one exactly when $q$ is a power of $3$).

**Definition 4.4.** A set $F$ of points is a *segment set* if for every $p\in F$ the other points of $F$ collinear with $p$ all lie on one line through $p$; equivalently, there are no $p,p',p''\in F$ with $p,p'$ collinear, $p',p''$ collinear, and $p,p''$ not collinear (a path of two collinearities that *turns* at $p'$).

Non-collinear sets are segment sets, and so is any subset of the point set of a set of pairwise opposite lines. A segment set has at most $(q+1)(q^3+1)$ points, with equality exactly for the point set of a spread (`D7_HEXAGON.md`, Proposition 1.4: count the lines meeting $F$ in exactly one point).

**Theorem 4.5 (Theorem B of `D7_HEXAGON.md`).** Such a transition is repaired if and only if its freed set is a segment set.

*Why.* The key fact is that for any two elements $u,v$ of $\Gamma$ there is a point $p\notin F$ with $d(u,p)+d(p,v)\le 6$. If some shortest path from $u$ to $v$ has a point outside $F$, take it. Otherwise all points on all shortest paths lie in $F$; a shortest path with three consecutive points would turn, so the remaining cases are short ($u$ and $v$ equal, collinear, incident, or at distance $3$ or $4$), and each is settled by stepping off the line that carries the other points of $F$ (`D7_HEXAGON.md`, Lemma 4.1, seven cases). Then $u$, then $p$, then the line $\psi(p)$ in copy $j+k$, then $v$ has length $d(u,p)+1+d(p,\psi^{-1}(v))\le 7$. Conversely, if $p,p',p''\in F$ turn at $p'$ and $u\ne m'$ is a line through $p''$ ($m'$ the line through $p'$ and $p''$), the only routes of length at most $7$ from $u$ in copy $j$ to $\psi(p)$ in copy $j+k$ would cross at $p$, $p'$ or $p''$, all freed.

So with a duality ($q=3^h$) the whole point set of a spread can be freed on every transition, and no larger set.

## 4.4 Arbitrary matchings: local dualities

For a transition whose bijection $M$ (points of copy $j$ to lines of copy $j+k$) is not an isomorphism, it is enough that $M$ looks like a duality near the freed points.

**Theorem 4.6 (Theorem C of `D7_HEXAGON.md`).** The transition is repaired if the freed set $R$ satisfies:

(H1) no two points of $R$ are collinear;

(H2) no two lines of $M(R)$ are concurrent;

(H3) for every $x\in R$, $M$ maps the points collinear with $x$ onto the lines concurrent with $M(x)$ ($M$ is a *local duality* at $x$).

*Proof.* Let $u$ be in copy $j$ and $v$ in copy $j+k$; distances are taken inside each copy. (1) $u$ a point not in $R$: $u$, $M(u)$, then $v$: at most $1+6$. (2) $u$ a line, $v$ a point: the $q+1$ lines through $v$ are pairwise concurrent, so by (H2) at most one is in $M(R)$; take another, $b$, and $a=M^{-1}(b)\notin R$: $u$ to $a$, then $b$, then $v$: at most $5+1+1$. (3) $u$ a line, $v$ a line not in $M(R)$: $u$ to $M^{-1}(v)$, then $v$: at most $5+1$. (4) $u$ a line, $v=M(x)$ with $x\in R$: there is a point $z$ collinear with $x$ with $d(z,u)\le 3$; $z\notin R$ by (H1), and $M(z)$ is concurrent with $v$ by (H3): $v$ to $M(z)$, then $z$, then $u$: at most $2+1+3$. (5) $u=x\in R$, $v$ a point: there is a line $w$ concurrent with $M(x)$ with $d(w,v)\le3$; by (H3) $w=M(z)$ with $z$ collinear with $x$, and $z\notin R$: $x$ to $z$, then $w$, then $v$: at most $2+1+3$. (6) $u=x\in R$, $v$ a line: the same, with $d(w,v)\le 4$: at most $2+1+4$. $\square$

Such matchings are easy to build when $R$ is a set of pairwise opposite points (a *partial ovoid*) and $M(R)$ is to be a set of pairwise opposite lines (a *partial spread*) of the same size: then the sets of points collinear with different points of $R$ are disjoint, and so are the sets of lines concurrent with different lines of $M(R)$; send each $x\in R$ to a chosen line, the $q(q+1)$ points collinear with $x$ bijectively onto the $q(q+1)$ lines concurrent with it, and the remaining points arbitrarily onto the remaining lines (`D7_HEXAGON.md`, Proposition 5.2 and Corollary 5.3(a)). More generally $R$ may contain pairs at distance $4$ if $M(R)$ has the same pattern of pairs at distance $4$ (“mirrored sets”). For example the $q^2+1$ points of an elliptic quadric section $Q^-(3,q)$ of the quadric of $H(q)$ are pairwise opposite, for every $q$, and the Hermitian spread supplies pairwise opposite lines.

## 4.5 What the records use

In each case the structure is that of §4.2, every transition is repaired by Theorem 4.5 or 4.6, and the hub graph satisfies the distance condition; the specific sets and hub graphs were found by computer and checked (`D7_HEXAGON.md`, §§8 and 10).

<div class="center">

| cells                                | copies                                                | freed sets                                                                                                                             | elements                |
|:-------------------------------------|:------------------------------------------------------|:---------------------------------------------------------------------------------------------------------------------------------------|:------------------------|
| $(7,7)$, $(9,7)$, $(10,7)$, $(13,7)$ | $3$ copies of $H(q)$, one matching on all transitions | the same set $R$ on every transition, $M$ a local duality on $R$ (pairwise opposite points plus a few, mirrored); $|R|=81,295,229,768$ | $6N+2|R|$               |
| $(11,7)$, $(12,7)$                   | $3$ or $5$ copies of $H(9)$, a duality                | the $7300$ points of a spread on every transition                                                                                      | $(2r+1)2N+2\cdot 7300r$ |
| $(14,7)$, $(16,7)$                   | $5$ copies, types $HDHDH$                             | friendly: identity, large non-collinear and non-concurrent sets; others: local dualities                                               | see `D7_HEXAGON.md` §8  |
| $(15,7)$                             | $7$ copies, types $HHDHDHD$                           | friendly: segment sets with some collinear pairs; others: local dualities                                                              |                         |

</div>

With classical ingredients only (the $q^2+1$ points of an elliptic quadric section, $q^2+1$ lines of a Hermitian spread, and an explicit hub graph built from a projective plane with pendant trees) the same theorems give $n_b(q+2,7)\ge 6N+2(q^2+1)$ for every $q\ge5$ (`D7_HEXAGON.md`, Corollary 9.1).

# Appendix A. Coordinates and checks

*Coordinates.* Explicit coordinates for every construction: `research/theorems/POLISHED.md` (§2 for the hats, §§3–5 for diameter $4$, §§6–7 for diameter $6$; on branch `claude/thm-polish-2oddll`), `research/plus2/coords/coords.tex` (the hats, with a hand-checkable proof), and `research/theorems/D7_HEXAGON.md` (diameter $7$; branch `claude/d7-hexagon-theorems-4w1prt`).

*The completing matching of \[AL20\].* In coordinates, \[AL20\] (arXiv v1, p. 8) complete the three-hat structure by the pairs $(x,y)\sim[x,y]$ and $P_i\sim L_i$; with the index set $i\in\mathrm{GF}(q)\setminus\{0,1,a\}$ printed there, the four elements $P_1,P_a,L_1,L_a$ keep degree $q+1$, and $i\in\mathrm{GF}(q)^*$ gives a regular structure (`POLISHED.md`, Remark 2.7; we have not seen the journal version). Neither the order nor the diameter depends on the matching (§1.5).

*Checks.* The scripts are in `research/synthetic/checks/`, each with its output in a `.out` file. They build the classical geometries from coordinates and then use only incidence; each runs in a few seconds.

- `check_d3.py` (Section 1): both hat constructions from rules (R1)– (R6) on a plane given by its incidence relation; equality with the coordinate construction of `coords.py` for $q=4,5,7,8,9$ and every admissible $(a,c)$; the gadget tables; the matching of Figure 1; the crossed doubling and the patches (Proposition 1.2, Lemma 1.3, including the extra far pair at $q=3$); the broken pairs and their repairs; every line of Table 4; degrees and the deficient elements (Lemma 1.4); the duality (Lemma 1.6); diameter $3$; the changes of §1.7. Planes: $\mathrm{PG}(2,q)$, $q=3,4,5,7$, and the Dickson nearfield plane of order $9$, with random frames.

- `check_d4.py` (Section 2): Theorem 2.2 on random weights, shadow lines and stand-ins in $W(3)$ and $\mathrm{AS}(3)$; $\mathrm{AS}(q)$ built from $W(q)$ by Payne derivation using only incidence, and properties (E1), (E2) of the two quadrics, for $q=3,5,7$; the $2$-ovoid and spread of $W(q)$ and the explicit completion, $q=3,5$; Delorme’s construction on $W(3)$; ovoid and spread of $W(2)$; the $(7,4)$ example.

- `check_d6.py` (Section 3): in $H(2)$ and $H(3)$: the spread, free points, whiskers, an exact whisker set (the formula of `POLISHED.md` for $q=3$, an exact-cover search for $q=2$), (L0) with equality, (L1), the components, the counting identity, the doubling (diameter $6$, maximum degree $q+m$, the count), the sheets, and Theorem R.

- `check_d7.py` (Section 4): Theorem 4.2 with random matchings on $H(2)$, $r=1,2$; Theorem 4.5 on $H(3)$ (a spread’s point set and a non-collinear set are repaired, a turning triple is not); Theorem 4.6 on $H(3)$ with a local duality at three pairwise opposite points (and a random bijection at the same set is not repaired); a three-copy structure with hubs on $H(3)$, diameter $7$.

The record values themselves were checked by the lab’s coordinator with all-pairs breadth-first search (`research/coordinator_check/`).

<div class="thebibliography">

99 G. Araujo-Pardo and N. López, On new record graphs close to bipartite Moore graphs, Graphs Combin. **38** (2022), no. 4, Paper 110; arXiv:2005.02427. J. Bamberg, M. Law and T. Penttila, Tight sets and $m$-ovoids of generalised quadrangles, Combinatorica **29** (2009), 1–17. C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. **6** (1985), 291–302. J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A **29** (1980), 87–93. J. Tits, Sur la trialité et certains groupes qui s’en déduisent, Publ. Math. IHÉS **2** (1959), 13–60. H. Van Maldeghem, Generalized Polygons, Birkhäuser, 1998. S. E. Payne, Nonisomorphic generalized quadrangles, J. Algebra **18** (1971), 201–212. S. E. Payne and J. A. Thas, Finite Generalized Quadrangles, 2nd ed., European Mathematical Society, 2009.

</div>
