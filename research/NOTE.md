# Large bipartite graphs of diameter 4 from generalized quadrangles

Authors: TBD

Draft, 2026-10-18.

> **Superseded (2026-10-25):** see `research/theorems/POLISHED.md` and the revised `research/geometry/geometry.tex`.
> In particular §7 below is out of date: Theorem B with stand-ins and Corollary C1 (directly in $W(3,q)$) are now Lean-checked,
> and open problem 3 is settled (at most $q^2-q+2$ shadow lines).

## Abstract

Let $n_b(\Delta,4)$ be the largest order of a bipartite graph with maximum degree $\Delta$ and diameter 4. When $\Delta-1$ is a prime power, the incidence graph of a generalized quadrangle of order $(\Delta-1,\Delta-1)$ meets the bipartite Moore bound. For the other degrees we add copies of vertices to the incidence graph of a generalized quadrangle (GQ). We prove three results.

- **Theorem A.** For every odd prime power $q$, the Ahrens–Szekeres quadrangle $AS(q)$ has a weighted 2-ovoid made of two elliptic quadrics. This gives a $(q+2)$-regular bipartite graph of diameter 4 and order $2q^2(q+2)$.
- **Theorem B.** A general copy theorem for any GQ of order $(s,t)$, with point copies, line copies and "stand-ins". As a consequence, $n_b(\Delta,4)\ge 2q^2\Delta$ for every prime power $q\le\Delta-1$.
- **Proposition C.** An explicit partition of $W(3,q)$, $q$ odd, into 2-ovoids, made of orbits of a cyclic group. We give a short proof. Dually it gives an exact 2-cover of $Q(4,q)$, and so $n_b(q+3,4)\ge 2(q^2+1)(q+3)$.

These improve the table of largest known bipartite graphs at $(\Delta,D)=(11,4),(13,4),(15,4),(16,4)$. Together with an earlier $(7,4)$ graph, this improves every open diameter-4 entry with $\Delta\le 16$.

## 1. Introduction

**The problem.** A bipartite graph with maximum degree $\Delta$ and diameter $D$ has at most

$$M_b(\Delta,D)=2\bigl(1+(\Delta-1)+(\Delta-1)^2+\dots+(\Delta-1)^{D-1}\bigr)$$

vertices (the bipartite Moore bound). Let $n_b(\Delta,D)$ be the largest order such a graph can have. Graphs that meet the bound are the incidence graphs of generalized polygons. For $D=4$ these are generalized quadrangles of order $(\Delta-1,\Delta-1)$. Such GQs are known exactly when $\Delta-1$ is a prime power ($W(3,q)$ and $Q(4,q)$), and none is known for any other order. So at $D=4$ the open cells are the degrees with $\Delta-1$ not a prime power. In the usual table range $3\le\Delta\le 16$ these are

$$\Delta\in\{7,11,13,15,16\},\qquad M_b(\Delta,4)=518,\ 2222,\ 3770,\ 5910,\ 7232 .$$

**Prior constructions.** Delorme and Farhi [DF84] introduced vertex duplication: a new vertex with the same neighbours as an old one does not increase the diameter (when $D\ge2$). Delorme [D85, Sec. 7–8] applied duplication to GQ incidence graphs. He copied a set of points that are pairwise at distance 4 (an ovoid-type set) and kept the graph bipartite. The table entries before this note are his: $346$ at $\Delta=7$, $1734$ at $11$, $3064$ at $13$, $4946$ at $15$, and $5134$ at $16$. For $\Delta=q+2$ the first four equal $2q^3+3q^2+3q+6$ with $q=5,9,11,13$.

Two other related papers. Araujo-Pardo, Dalfó, Fiol and López [ADFL21, Sec. 4] double every line of a GQ to get biregular graphs (semi-double graphs). Araujo-Pardo and López [AL20, Problem 4] ask for diameter-4 and diameter-6 versions of their diameter-3 construction.

**What is new.**

1. *Weighted ovoids of $AS(q)$* (Section 3). The quadrangle $AS(q)$ has order $(q-1,q+1)$. Its incidence graph has degrees $q$ and $q+2$. Point copies that add exactly 2 to every line make it $(q+2)$-regular. $AS(q)$ has no ovoid-like *set* that does this (an ILP rules it out for $q=3,5$). But a *multiset* does: two elliptic quadrics that meet in one point, with that point counted twice. This gives $n_b(q+2,4)\ge 2q^2(q+2)$, which beats Delorme's family by $q^2-3q-6$ for every $q\ge5$.
2. *Copies of lines, and stand-ins* (Section 2). We copy lines as well as points. A line copy may attach to copies of points ("stand-ins") instead of the originals. One theorem covers all the variants, for any GQ of order $(s,t)$.
3. *An explicit 2-cover of $Q(4,q)$* (Sections 4–5). We give a short proof that, in the cyclic model of $PG(3,q)$, two orbits of a Singer subgroup of order $q^2+1$ form a 2-ovoid of $W(3,q)$. Dually this is a set of $2(q^2+1)$ lines of $Q(4,q)$ with every point on exactly two of them. At $q=13$ it gives $n_b(16,4)\ge5440$.

To our knowledge (literature check of 2026-10-18), items 1 and 2 are new, and so is their use in the degree–diameter problem. For item 3, the existence of such partitions is known [BLP09; cited in FWX19]; see Section 5.3.

## 2. The copy lemma and stand-ins

Let $S=(P,L)$ be a GQ of order $(s,t)$, with $s,t\ge1$. It has $(s+1)(st+1)$ points and $(t+1)(st+1)$ lines. Each line has $s+1$ points and each point is on $t+1$ lines. For $p\notin\ell$ there is exactly one point of $\ell$ collinear with $p$. In the incidence graph $G(S)$ two points are at distance 2 or 4, two lines at distance 2 or 4, and a point and a line at distance 1 or 3. So $G(S)$ is bipartite with diameter 4.

**Copy lemma** (after [DF84]). Let $G$ be a graph. Form $H$ by adding copies of some vertices, where a copy $v'$ of $v$ is adjacent to the *original* neighbours of $v$ (and to nothing else). Equivalently, two vertices of $H$ are adjacent exactly when their underlying vertices are adjacent in $G$ and at least one of the two is original. (This is the `blowup` of the Lean proof.) Note that an original vertex also gains the copies of its neighbours, so a copy is in general *not* a twin of its original. Write $\hat x$ for the underlying vertex of $x\in V(H)$. Then, for $x\ne y$:

- if $d_G(\hat x,\hat y)=k\ge2$, then $d_H(x,y)\le k$: if $\hat x=v_0,v_1,\dots,v_k=\hat y$ is a shortest path, then $x,v_1,\dots,v_{k-1},y$ is a path in $H$, because $v_1,\dots,v_{k-1}$ are original;
- if $\hat x=\hat y$, then $d_H(x,y)=2$, through any original neighbour;
- if $\hat x\sim\hat y$, then $d_H(x,y)=1$ when one of them is original, and $d_H(x,y)\le3$ (path $x,\hat y,\hat x,y$) when both are copies.

So $d_H(x,y)\le\max(d_G(\hat x,\hat y),3)$, and the diameter stays at most $D$ when $D\ge3$. In particular $d_H(v',w)\le\max(d_G(v,w),2)$ whenever $w$ is original.

**Construction.** Fix $\Delta\ge\max(s,t)+1$.

- *Point copies.* A weight $w:P\to\mathbb Z_{\ge0}$. Point $p$ gets $w(p)$ copies, and each copy is joined to every original line through $p$.
- *Line copies.* A multiset $M$ of lines. A copy $y_\ell$ of $\ell\in M$ is joined, for each $p\in\ell$, to one *stand-in* $\sigma_\ell(p)$. The stand-in is either $p$ itself or one of the copies of $p$.

**Theorem B.** Let $H$ be the graph above.

1. $H$ is bipartite with diameter 4.
2. Its maximum degree is at most $\Delta$ exactly when both of these hold:
   - $\sum_{p\in\ell}w(p)\le\Delta-s-1$ for every line $\ell$;
   - each of the $1+w(p)$ stand-ins of a point $p$ serves at most $\Delta-t-1$ line copies. (So $p$ lies on at most $(\Delta-t-1)(1+w(p))$ entries of $M$.)
3. $|V(H)|=(s+t+2)(st+1)+\sum_p w(p)+|M|$.

*Proof.* Point copies and stand-ins lie on the point side, and line copies on the line side, so $H$ is bipartite. The degree conditions come from counting. An original line has $s+1$ points and gains $\sum_{p\in\ell}w(p)$ copies. A stand-in has degree $t+1$ plus the number of line copies it serves.

*Distances.* Delete the line copies. What is left is the copy graph of $G(S)$ with point copies only, so the copy lemma gives distance at most 4 between any two remaining vertices. Adding vertices back cannot increase these distances. Every stand-in of $r$ is adjacent to every original line through $r$. For pairs that involve a line copy $y_m$:

- *A point $p$, or a copy of it, to $y_m$.* If $p\notin m$, let $r\in m$ be the point collinear with $p$, on a line $k$. Then $p - k - \sigma_m(r) - y_m$. If $p\in m$, pick $r\in m$ with $r\ne p$, and use $p - m - \sigma_m(r) - y_m$. Length at most 3.
- *An original line $\ell$ to $y_m$.* If $\ell$ meets $m$ in $r$ (or $\ell=m$), use $\ell - \sigma_m(r) - y_m$. If they are disjoint, pick collinear $u\in\ell$ and $r\in m$ on a line $k$, and use $\ell - u - k - \sigma_m(r) - y_m$.
- *$y_\ell$ to $y_m$.* Pick $u\in\ell$ and $r\in m$, equal or collinear, and a line $k$ through both. Then $y_\ell - \sigma_\ell(u) - k - \sigma_m(r) - y_m$.

Now take two non-collinear original points. They have no common neighbour: a line copy is adjacent only to stand-ins of the points of one line, and an original point stands in only for itself. So the diameter is exactly 4. $\square$

When every stand-in is the original point, $y_\ell$ is adjacent exactly to the original points of $\ell$, and $H$ is the copy graph of the copy lemma (point copies and line copies together). This special case is the "line multiset" construction of [research/gq4/THEOREM.md], and it is the case proved in Lean (Section 7).

Delorme's duplication of an ovoid-type set [D85, Sec. 8(a)] is a point-copy construction of this kind.

**Definitions.** A *weighted $m$-ovoid* is a weight $w$ with $\sum_{p\in\ell}w(p)=m$ for every line $\ell$. A *weighted $m$-cover* is a multiset of lines with every point on exactly $m$ entries.

**Corollary B1 (exact weights give $2\Delta(st+1)$).** Suppose $S$ has a weighted $(\Delta-s-1)$-ovoid and a weighted $(\Delta-t-1)$-cover. Then $n_b(\Delta,4)\ge 2\Delta(st+1)$.

*Proof.* Use Theorem B with all stand-ins original. Double counting gives $\sum w=(\Delta-s-1)(st+1)$ and $|M|=(\Delta-t-1)(st+1)$. The order is $(st+1)\bigl(s+t+2+(\Delta-s-1)+(\Delta-t-1)\bigr)=2\Delta(st+1)$. $\square$

For $Q(4,q)$ this is $2\Delta(q^2+1)$, and for $AS(q)$ it is $2\Delta q^2$.

## 3. Theorem A: $AS(q)$ and two elliptic quadrics

**The quadrangle.** Let $q$ be odd. Let $\mathcal G=GF(q)\times GF(q)^2$ with product

$$(a,w)(a',w')=(a+a'+\det(w,w'),\ w+w'),\qquad \det((b,c),(b',c'))=bc'-cb'.$$

- The points are the $q^3$ elements of $\mathcal G$.
- The lines are the left cosets of the $q+1$ subgroups $Z_d=\{(0,\lambda d)\}$, one for each direction $d\in PG(1,q)$, and of $Z=\{(\mu,0)\}$.
- Explicitly, a coset line is $\{(a_0+\lambda D,\ w_0+\lambda d):\lambda\in GF(q)\}$ with $D=\det(w_0,d)$. A fibre is $\{(a_0+\mu,\ w_0)\}$.

This is Payne's derivation $P(W(q),x)$ at a point $x$ [P71]. It is a GQ of order $(q-1,q+1)$, isomorphic to the Ahrens–Szekeres quadrangle $AS(q)$ for $q$ odd [AS69; PT, Ch. 3]. In coordinates, $(a,(b,c))$ is the vector $(a,1,b,c)$ and $W(q)$ is given by $u_0v_1-u_1v_0+u_2v_3-u_3v_2$. (We also checked every GQ axiom by computer for $q=3,\dots,13$.)

**The quadrics.** Fix a non-square $\varepsilon\in GF(q)$ and let $N(b,c)=b^2-\varepsilon c^2$. This form is anisotropic: $N(w)=0$ only for $w=0$. For $c\ne0$ let $Q_c=\{(cN(w),\,w):w\in GF(q)^2\}$. Together with $x$, $Q_c$ is the elliptic quadric $v_0v_1=cN(v_2,v_3)$.

**Theorem A.** If $c_1c_2=1/(4\varepsilon)$, then the multiset $Q_{c_1}+Q_{c_2}$ is a weighted 2-ovoid of $AS(q)$. The two sets meet only in $e=(0,0)$, which gets weight 2.

*Proof.*

- *Fibres.* Each $Q_c$ has exactly one point over each $w$, so each fibre meets the multiset in $1+1$ points.
- *Coset lines.* The point with parameter $\lambda$ on the line $\{(a_0+\lambda D, w_0+\lambda d)\}$ lies in $Q_c$ exactly when
  $$cN(d)\lambda^2+(cB-D)\lambda+cN(w_0)-a_0=0,\qquad B=N(w_0+d)-N(w_0)-N(d).$$
  Since $N(d)\ne0$, this is a true quadratic, so it has $1+\chi(\Delta_c)$ roots. Here $\chi$ is the quadratic character, with $\chi(0)=0$.
- *The identity.* Write $w_0=(b_0,c_0)$ and $d=(b_1,c_1)$. Then $B=2(b_0b_1-\varepsilon c_0c_1)$ and
  $$B^2-4N(w_0)N(d)=4\varepsilon(b_0c_1-c_0b_1)^2=4\varepsilon D^2 .$$
  So the discriminant is
  $$\Delta_c=(cB-D)^2-4cN(d)(cN(w_0)-a_0)=4cN(d)\,(a_0-a^*_c),\qquad a^*_c=-\frac{4\varepsilon cD^2-2BD+D^2/c}{4N(d)} .$$
- *Same centre.* $a^*_{c_1}-a^*_{c_2}=-\frac{D^2}{4N(d)}\,(c_1-c_2)\bigl(4\varepsilon-\tfrac1{c_1c_2}\bigr)$, which is $0$ when $c_1c_2=1/(4\varepsilon)$. Call the common value $a^*$.
- *Count.* The line meets the multiset in
  $$2+\chi\bigl(N(d)(a_0-a^*)\bigr)\,\bigl(\chi(c_1)+\chi(c_2)\bigr)$$
  points. Since $\chi(c_1)\chi(c_2)=\chi(1/(4\varepsilon))=\chi(\varepsilon)=-1$, we have $\chi(c_1)+\chi(c_2)=0$, and the count is 2. A double root ($a_0=a^*$) gives one point in each set.
- *Intersection.* $c_1\ne c_2$, because $c_1^2=1/(4\varepsilon)$ is impossible for a non-square. So $c_1N(w)=c_2N(w)$ forces $N(w)=0$, that is $w=0$. $\square$

**Corollary A1.** For every odd prime power $q$, $n_b(q+2,4)\ge 2q^2(q+2)$. The graph is $(q+2)$-regular.

*Proof.* Add one new point for each entry of $Q_{c_1}+Q_{c_2}$ (so $e$ gets two), joined to the $q+2$ lines through its point. Every line has $q$ points and gains exactly 2 neighbours. Every original point is on $q+2$ lines, and every copy has degree $q+2$. The copy lemma gives diameter 4. The order is $q^3+(q+2)q^2+2q^2=2q^2(q+2)$. $\square$

At $q=9,11,13$ this gives $1782$, $3146$ and $5070$, against the table values $1734$, $3064$ and $4946$.

Remarks:

- Weights are needed. An ILP (HiGHS) shows that $AS(3)$ has no 1- or 2-ovoid without repeated points, and $AS(5)$ has no $m$-ovoid for $m=1,\dots,4$. The largest partial 2-ovoid of $AS(5)$ has 49 points (proved optimal). With repeats allowed the ILP found 50, in exactly the shape of Theorem A.
- The graph is regular, so no copy scheme on $AS(q)$ does better at $\Delta=q+2$.

## 4. $Q(4,q)$ with copies of lines

$Q(4,q)$ is the GQ of points and lines on a non-singular quadric of $PG(4,q)$. It has order $(q,q)$ and $(q+1)(q^2+1)$ points. It has ovoids for every $q$ (an elliptic quadric section). It has spreads exactly when $q$ is even [PT, Ch. 3]. It is the point–line dual of $W(3,q)$ [PT, Ch. 3], so an $m$-ovoid of $W(3,q)$ is an $m$-cover of $Q(4,q)$.

Take $w=j\cdot\mathbf 1_O$ for an ovoid $O$, and a line multiset $M$ with every point on at most $j$ entries, all stand-ins original. Theorem B gives a bipartite graph of maximum degree $q+1+j$, diameter 4 and order

$$2(q+1)(q^2+1)+j(q^2+1)+|M| .$$

**$j=1$: partial spreads.** Here $M$ is a set of pairwise disjoint lines.

- For odd $q$, a partial spread has at most $q^2-q+1$ lines (Tallini; see [CDPS22]).
- Tallini [T88] constructs, for every odd $q$, a maximal partial ovoid of $W(3,q)$ with $2q+1$ points [as cited in CDPS22, Sec. 1; we have not seen the construction itself]. Dually this is a partial spread of $Q(4,q)$ with $2q+1$ lines.
- So $n_b(q+2,4)\ge 2q^3+3q^2+4q+4$ for odd $q$, which is $q-2$ above Delorme's $2q^3+3q^2+3q+6$.
- Theorem A is larger still (by $q^2-4q-4>0$ for $q\ge5$).
- Computer searches found partial spreads (pairwise disjoint lines) of 51, 72 and 92 lines for $q=9,11,13$ (`research/gq4/spreads/spread_q{9,11,13}_s{51,72,92}.json`). `research/gq4/from_spread.py` checks disjointness and builds the copy graph with all stand-ins original. This gives $1773$, $3122$ and $5022$; the last two were records before Theorem A.
- The $1774$ graph at $q=9$ was found earlier by evolutionary search (2026-10-10). Taken apart, it is a GQ(9,9) incidence graph with 82 point copies and 52 line copies. One pair of the copied lines meets in a point, and that point and its copy each serve one of them (one stand-in). There is also one extra edge at one line copy. Without that edge the graph still passes `lib.is_valid`.

**$q=5$, $\Delta=7$.** Stand-ins help here. An ILP over $Q(4,5)$ with one ovoid copy and line copies with stand-ins shows that the optimum is exactly 21 line copies, for order $2\cdot6\cdot26+26+21=359$. Every ovoid of $Q(4,p)$, $p$ prime, is an elliptic quadric [BGS06], so the choice of ovoid does not matter. We have two 359-vertex graphs, and both use stand-ins. (Twin counts say nothing here, since a copy is not a twin of its original even without stand-ins.)

- The ILP graph (`research/gq4x/graphs/q4_share_q5_n359.json`, 1218 edges) uses stand-ins by construction. In it, 4 points each lie on two copied lines, one served by the point and one by its copy.
- The evolutionary-search graph (the record file, 1239 edges, found 2026-10-10) can be taken apart the same way. It is a GQ(5,5) incidence graph (6-regular, 312 vertices, girth 8; we did not identify which GQ) with 26 point copies and 21 line copies. Each line copy has one extra edge beyond its 6 stand-ins. Removing those 21 edges leaves a Theorem B graph in which 5 points each lie on two copied lines, so stand-ins are essential there too. The stripped graph still passes `lib.is_valid`.

Note that $AS(5)$ gives only 350.

**$j\ge2$: covers.** Suppose $M$ is an exact $j$-cover, meaning every point is on exactly $j$ entries. Then Corollary B1 with $s=t=q$ and $\Delta=q+1+j$ gives order $2(q^2+1)(q+1+j)$. Bamberg, Law and Penttila [BLP09] construct $m$-ovoids of $W(3,q)$ for $q$ odd and every even $m$; dually these are $m$-covers of $Q(4,q)$. Section 5 gives an explicit 2-cover with a short proof, and $j/2$ copies of it form a $j$-cover.

**Corollary B2 (all degrees).** For every prime power $q$ and every $\Delta\ge q+1$, $n_b(\Delta,4)\ge 2q^2\Delta$.

*Proof.* There are three cases.

- *$q$ even.* $Q(4,q)$ has an ovoid $O$ and a spread $\Sigma$. Take $j=\Delta-q-1$ copies of each. Corollary B1 gives $2(q^2+1)\Delta$.
- *$q$ odd, $\Delta$ even.* Here $j=\Delta-q-1$ is even. Take $j$ copies of an ovoid and $j/2$ copies of a 2-cover (Section 5). Corollary B1 gives $2(q^2+1)\Delta$.
- *$q$ odd, $\Delta$ odd.* Then $\Delta\ge q+2$. In $AS(q)$ (order $(q-1,q+1)$), take $(\Delta-q)/2$ copies of $Q_{c_1}+Q_{c_2}$, which is a weighted $(\Delta-q)$-ovoid. Take $\Delta-q-2$ copies of the fibre spread, which is a $(\Delta-q-2)$-cover. Corollary B1 gives $2q^2\Delta$. $\square$

In the table range, odd $\Delta$ with $\Delta-1$ not a prime power uses $AS(\Delta-2)$ ($\Delta=7,11,13,15$). The only even such cell is $\Delta=16$, which uses $Q(4,13)$ with $j=2$.

## 5. An explicit 2-cover of $Q(4,q)$ from a Singer subgroup

### 5.1 Setting

Let $q$ be an odd prime power, $F=GF(q)$, $K=GF(q^2)$ and $E=GF(q^4)$, with $g$ a primitive element of $E$.

- Model $PG(3,q)$ as $E^*/F^*$. The point $\langle g^i\rangle$ has index $i$ mod $N=(q^4-1)/(q-1)=(q+1)(q^2+1)$.
- Write $\bar x=x^{q^2}$ (the involution of $E/K$) and $x'=x^q$ on $K$. Let $\mathrm{N}(x)=x\bar x\in K$.
- Let $d=g^{(q^2+1)/2}$. Then $\bar d=-d$, and $h:=d^2=g^{q^2+1}$ generates $K^*$.
- Let $B(x,y)=\mathrm{Tr}_{E/F}(d\,x\bar y)$. Since $\mathrm{Tr}_{E/F}=\mathrm{Tr}_{K/F}\circ\mathrm{Tr}_{E/K}$,
  $$B(x,y)=\mathrm{Tr}_{K/F}\bigl(d(x\bar y-\bar xy)\bigr).$$
  This form is alternating and non-degenerate. Let $W(3,q)$ be its symplectic quadrangle.
- If $\lambda=g^{(q+1)k}$, then $\lambda\bar\lambda=\lambda^{q^2+1}\in F^*$, so $x\mapsto\lambda x$ scales $B$ and preserves $W(3,q)$.
- The orbits of $\langle g^{q+1}\rangle$ are the classes $C_a=\{\langle g^i\rangle: i\equiv a \pmod{q+1}\}$, each of size $q^2+1$.
- The point $\langle g^i\rangle$ has $\mathrm{N}(g^i)=h^i$. The group $K^*/F^*$ is cyclic of order $q+1$, generated by $h$. So $\langle x\rangle\in C_a$ exactly when $\mathrm{N}(x)\in h^aF^*$.

These classes are Ebert's partition of $PG(3,q)$ into $q+1$ elliptic quadrics [E85].

**Proposition C.** For $q$ odd:

1. Every line of $PG(3,q)$ meets each $C_a$ in at most 2 points.
2. Every totally isotropic line of $W(3,q)$ meets $C_a\cup C_{q-a}$ in exactly 2 points.

So the $(q+1)/2$ sets $C_a\cup C_{q-a}$, $0\le a\le (q-1)/2$, partition $W(3,q)$ into 2-ovoids. The pairing $a\leftrightarrow q-a$ has no fixed point, since $2a\equiv-1\pmod{q+1}$ is impossible for $q+1$ even.

### 5.2 Proof

Let $\ell=\langle x,y\rangle_F$ be a line, and let $z=sx+ty$. Then

$$\mathrm{N}(z)=As^2+\beta st+Ct^2,\qquad A=\mathrm{N}(x),\ C=\mathrm{N}(y),\ \beta=x\bar y+\bar xy,$$

with all three in $K$. Put $u=x\bar y-\bar xy$. Since $\bar u=-u$, we can write $u=dk_0$ with $k_0\in K$. Also

$$\mathcal E:=\beta^2-4AC=u^2=hk_0^2,\qquad B(x,y)=\mathrm{Tr}_{K/F}(hk_0).$$

*Membership in a class.* Fix $\omega\in K^*$ with $\omega'=-\omega$. For $\mu\in K^*$ let $\nu=\omega/\mu$. For $k\in K$ we have $\mathrm{Tr}_{K/F}(\nu k)=0$ exactly when $k\in\mu F$. So $z\in C_\mu:=\{\langle z\rangle:\mathrm{N}(z)\in\mu F^*\}$ exactly when $(s:t)$ is a zero of the binary form

$$f_\nu(s,t)=\mathrm{Tr}(\nu A)s^2+\mathrm{Tr}(\nu\beta)st+\mathrm{Tr}(\nu C)t^2 .$$

*Part 1 (caps).* Suppose $f_\nu\equiv0$. Then $A$, $C$ and $\beta$ all lie in $\mu F$.

- If $\mathcal E\ne0$, then $h=\mathcal E/k_0^2\in\mu^2F^*/k_0^2$. But $F^*\subset (K^*)^2$, since $[K^*:F^*]=q+1$ is even. So $h$ would be a square in $K^*$, which is false because $h$ generates $K^*$.
- If $\mathcal E=0$, then $\mathrm{N}(sx+ty)=\mu(as^2+bst+ct^2)$ with $b^2=4ac$ and $a\ne0$. This vanishes at $(s:t)=(-b:2a)$, which is impossible because $\mathrm N(z)\ne0$ for $z\ne0$.

So $f_\nu\not\equiv0$, and it has exactly $1+\chi(D(\nu))$ projective zeros, where

$$D(\nu)=\mathrm{Tr}(\nu\beta)^2-4\,\mathrm{Tr}(\nu A)\,\mathrm{Tr}(\nu C).$$

In particular there are at most 2.

*Part 2.* Expand with $\mathrm{Tr}(\nu k)=\nu k+\nu'k'$:

$$D(\nu)=\mathrm{Tr}_{K/F}(\nu^2\mathcal E)+\nu\nu'\,P,\qquad P=2\beta\beta'-4AC'-4A'C\in F .$$

If $\ell$ is totally isotropic, then $hk_0\in\omega F$, so $h\mathcal E=(hk_0)^2=:e\in F$. Then

$$\mathrm{Tr}(h^2\nu'^2\mathcal E)=e\,(h\nu'^2+h'\nu^2)=hh'\cdot e\Bigl(\frac{\nu^2}{h}+\frac{\nu'^2}{h'}\Bigr)=\mathrm{N}_{K/F}(h)\,\mathrm{Tr}(\nu^2\mathcal E).$$

Since $\mathrm{N}_{K/F}(h\nu')=\mathrm{N}_{K/F}(h)\,\nu\nu'$, this gives the key identity

$$D(h\nu')=\mathrm{N}_{K/F}(h)\,D(\nu).$$

$h$ generates $K^*$, so $\mathrm{N}_{K/F}(h)=h^{q+1}$ generates $F^*$ and is a non-square. Hence $\chi(D(h\nu'))=-\chi(D(\nu))$.

*Which classes pair up.* The class that belongs to $h\nu'$ is $\mu^\dagger\equiv\omega/(h\nu')=\omega/(-h\omega/\mu')\equiv\mu^q/h\equiv(h\mu)^{-1}$ modulo $F^*$. Here we used $\mu^{q+1}\in F^*$. So $\mu\mu^\dagger h\in F^*$. In terms of indices, $a+a^\dagger+1\equiv0$, that is $a^\dagger\equiv q-a\pmod{q+1}$. Scaling $\nu$ by $F^*$ multiplies $D$ by a square, so the count depends only on the class.

*Conclusion.* A totally isotropic line meets $C_a\cup C_{q-a}$ in $(1+\chi(D))+(1-\chi(D))=2$ points. When $D=0$, both counts are 1. $\square$

Remarks:

- *Lines of the regular spread.* The lines $xK$ ($u=0$) are totally isotropic. On such a line $\mathrm N(x\kappa)=\mathrm N(x)\kappa^2$ for $\kappa\in K$. Squaring is 2-to-1 on $K^*/F^*$, so the line meets each of the $(q+1)/2$ classes with the same parity as $\mathrm N(x)$ in exactly 2 points, and the other classes not at all. Since $a$ and $q-a$ have opposite parity, the count is again 2. This fits Ebert's result that some line is tangent to both $E_i$ and $E_j$ exactly when $i+j$ is odd [E85, Cor. 1 and Thm 5, as quoted in CMPS21, Lemma 5.3].
- *Other pairings.* The proof uses only that $d^2$ is a non-square of $K$. Replacing $d$ by any $\delta$ with $\bar\delta=-\delta$ gives a symplectic form for which $C_a\cup C_b$ is a 2-ovoid exactly when $\mu_a\mu_b\delta^2\in F^*$. So every pair of classes of opposite parity is a 2-ovoid of one of these symplectic quadrangles.

*Computer check.* `research/gq4y/w3_singer.py` tests every pair of classes for $q=3,5,7,11,13$. Exactly the pairs $\{a,q-a\}$ are 2-ovoids. `research/gq4y/w3_singer_pp.py` does the same in $GF(p^{4e})$ for non-prime $q=9$, $25$, $27$, plus $q=3,5,7$.

### 5.3 Literature

- Ebert [E85] partitions $PG(3,q)$ into $q+1$ elliptic quadrics, the orbits of a subgroup of order $q^2+1$ of a Singer cycle. These are the classes $C_a$.
- Feng, Wang and Xiang [FWX19, Sec. 1] state that for $p$ odd "there is a partition of $W(3,p^e)$ into 2-ovoids", citing Bamberg–Law–Penttila [BLP09].
- Cossidente, Culbert, Ebert and Marino [CCEM08] construct transitive 2-ovoids of $W(3,q)$ whose stabilisers lie in a Singer-type group (as cited in [FLT22, Remark 3.21(2)]).
- We could not read [BLP09] or [CCEM08] (both behind paywalls), so we cannot say whether their 2-ovoids are exactly $C_a\cup C_{q-a}$. Proposition C is very likely a known object. The proof above is self-contained, and we have not seen it in this form.

### 5.4 Consequences

The Klein correspondence maps points of $W(3,q)$ to lines of $Q(4,q)$, and totally isotropic lines to points. So $C_a\cup C_{q-a}$ becomes a set of $2(q^2+1)$ lines of $Q(4,q)$ with every point on exactly two of them. `research/gq4y/to_q4.py` carries this out explicitly.

**Corollary C1.** For every odd prime power $q$ and every even $j\ge2$, $n_b(q+1+j,4)\ge2(q^2+1)(q+1+j)$. In particular $n_b(q+3,4)\ge2(q^2+1)(q+3)$.

*Proof.* Take $j$ copies of an ovoid of $Q(4,q)$ and $j/2$ of the 2-ovoids $C_a\cup C_{q-a}$, dualised. If $j>q+1$, repeat them. Then apply Corollary B1. $\square$

At $q=13$ the 2-cover has 340 lines, and the graph has order $2\cdot14\cdot170+2\cdot170+340=5440$, with degrees 14 and 16. The table value is 5134. Our previous best was 5357, from a partial 2-cover found by annealing. Without stand-ins, $5440=2(q^2+1)(q+3)$ is the most a $Q(4,13)$ copy graph of maximum degree 16 can have: each line takes at most 2 point copies and each point at most 2 line copies.

## 6. Table

Diameter 4, the open degrees with $\Delta\le16$. All five graphs were verified on 2026-10-18 by `scripts/verify_record.py` (Section 7).

| $(\Delta,D)$ | Moore bound | old table [D85] | new | construction | % of Moore |
|---|---|---|---|---|---|
| (7,4) | 518 | 346 | **359** | $Q(4,5)$ + 1 ovoid copy + 21 line copies with stand-ins (Thm B) | 69.3 |
| (11,4) | 2222 | 1734 | **1782** | $AS(9)$ + $Q_{c_1}+Q_{c_2}$ (Cor. A1), 11-regular | 80.2 |
| (13,4) | 3770 | 3064 | **3146** | $AS(11)$ + $Q_{c_1}+Q_{c_2}$ (Cor. A1), 13-regular | 83.4 |
| (15,4) | 5910 | 4946 | **5070** | $AS(13)$ + $Q_{c_1}+Q_{c_2}$ (Cor. A1), 15-regular | 85.8 |
| (16,4) | 7232 | 5134 | **5440** | $Q(4,13)$ + 2 ovoid copies + Singer 2-cover, 340 lines (Cor. C1) | 75.2 |

Graph files are in `records/bipartite_dd/`: `d7D4/359-spec-d7d4-g017-c11.json`, `d11D4/1782-gq4x-as_w2_q9_n1782.json`, `d13D4/3146-gq4x-as_w2_q11_n3146.json`, `d15D4/5070-gq4x-as_w2_q13_n5070.json` and `d16D4/5440-gq4-cover2_q13_n5440.json`.

## 7. Formal verification

**Graphs.** Every record graph is checked by three independent programs (`scripts/verify_record.py`):

1. the project's checker;
2. a networkx checker;
3. a from-scratch check: adjacency sets, an explicit 2-colouring, and a breadth-first search from every vertex for the exact diameter.

Output for the five graphs above (rerun 2026-10-18):

| graph | degrees | sides | edges | result |
|---|---|---|---|---|
| 359 | 6, 7 | 177 + 182 | 1239 | diameter 4, all three pass |
| 1782 | 11 | 891 + 891 | 9801 | diameter 4, all three pass |
| 3146 | 13 | 1573 + 1573 | 20449 | diameter 4, all three pass |
| 5070 | 15 | 2535 + 2535 | 38025 | diameter 4, all three pass |
| 5440 | 14, 16 | 2720 + 2720 | 42840 | diameter 4, all three pass |

**Theorems in Lean 4.** These are proved in Lean 4 with Mathlib on branch `lean-gqst` (as reported by the Lean sessions; not rebuilt for this note). `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no new axioms, no `native_decide`.

- *Order $(s,t)$ (`GQST.isBipartiteDegDiam`, `gqst`).* Take a GQ of order $(s,t)$, $w(p)$ copies of each point $p$ and $m(\ell)$ copies of each line $\ell$, for any $w:P\to\mathbb N$ and $m:L\to\mathbb N$. If the line sums of $w$ are at most $a$ and the point sums of $m$ are at most $b$, the graph is bipartite with maximum degree at most $\max(s+1+a,\,t+1+b)$ and diameter at most 4.

- *Order $(q,q)$ (`GQ4.isBipartiteDegDiam`, `gq4`).* The old statement for a GQ of order $(q,q)$ with $j$ copies of each point of a partial ovoid is derived from `gqst` (`gq4_of_gqst`).

The copy graph in Lean is the `blowup` of the copy lemma: adjacent exactly when the underlying vertices are adjacent and at least one is original. So `GQST.gqst` covers weighted point copies and line copies with all stand-ins original, for any GQ of order $(s,t)$. That includes Corollaries A1, B1, B2 and C1, and the constructions behind 1782, 3146, 5070, 5440, 3122 and 5022. It does not cover stand-ins (Theorem B in full), which the 359 graphs and the 1774 graph use. The GQ axioms used are the counts and the existence half of the GQ axiom. **Theorem A is fully formal** (branch `claude/lean-asq-bound-lk0k7y`): `ASq.isGQst` (AS(q) is a GQ of order $(q-1,q+1)$ over any finite field), `ASq.weighted_two_ovoid` ($Q_{c_1}+Q_{c_2}$ meets every line with total weight 2 when $c_1c_2=1/(4\varepsilon)$, $\varepsilon$ a non-square, odd characteristic) and `ASq.bound`: for every finite field of odd order $q$ there is a bipartite graph on $2q^2(q+2)$ vertices with maximum degree $q+2$ and diameter 4. Same three axioms. **Proposition C is formal too** (branch `claude/lean-final-singer-c-r9xece`, `SingerC.propC_subspace`): for every odd prime power $q$, every 2-dimensional totally isotropic $\mathbb F_q$-subspace of $\mathbb F_{q^4}$ has exactly $2(q-1)$ nonzero vectors in classes $a$ or $q-a$, i.e. exactly 2 points. Same three axioms. (The Klein-correspondence step from $W(3,q)$ to $Q(4,q)$ is not formalised; the $5440$ graph itself is kernel-checked.)

**Record graphs in the kernel.** $n_b(7,4)\ge359$ is kernel-checked (`nb_7_4` in `lean/BipartiteDD/Records.lean`, same three axioms). The record graphs 2510 ($(9,5)$), 1782, 3146, 5070 and 5440 are kernel-checked by staged checks that split the distance computation by radius (branches `lean-records2`, `claude/lean-records3-graphs-6719pq`; theorems `nb_9_5`, `nb_11_4_v2`, `nb_13_4_v2`, `nb_15_4_v2`, `nb_16_4_v2`), same three axioms.

## 8. Open problems

1. **Proposition C in the literature.** Identify the construction in [BLP09] or [CCEM08], and check whether it is the same as $C_a\cup C_{q-a}$.
2. **$(7,4)$.** Is $359$ optimal among GQ copy graphs at $\Delta=7$? The $Q(4,5)$ family with one ovoid copy is capped at 359 (ILP), and $AS(5)$ at 350. The Moore bound is 518.
3. **Line copies at $\Delta=q+2$.** With stand-ins, $Q(4,q)$ allows at most $q^2+1$ line copies with one ovoid copy, so at most $2(q^2+1)(q+2)$ vertices. That is $2q+4$ above Corollary A1. Do $q^2+1$ line copies with stand-ins exist for odd $q\ge7$? The best found are 52 (with one stand-in), 72 and 92 (partial spreads) for $q=9,11,13$, against 60, 96 and 140 needed just to match $AS(q)$.
4. **Weighted 3-ovoids of $AS(q)$.** They exist for $q=5,7$ (found by ILP), but none was found for $q=9,11,13$. They would not beat Corollary C1 at $\Delta=q+3$ ($2q^2(q+3)<2(q^2+1)(q+3)$), but their existence is a natural question. A weighted 3-ovoid invariant under $(a,w)\mapsto(\mathrm N(\zeta)a,\zeta w)$ cannot exist (parity argument).
5. **Other diameters.** At $D=3$ (projective planes) the open degrees in range are again 7, 11, 13 and 15. Our extension of the construction of [AL20] (2026-10-10) improves 11, 13 and 15 by 2 each (192, 276, 376). Does a weighted-copy analogue of Theorem A exist there? At $D=6$, the Feit–Higman condition rules out generalized hexagons of order $(q-1,q+1)$ ($st=q^2-1$ is never a square), so there is no direct analogue of $AS(q)$. Weighted distance-2 ovoids of $H(q)$ are untested. Octagons of order $(q-1,q+1)$ exist at $q=3$ (the Ree–Tits octagon of order $(2,4)$), and a weighted 2-ovoid there would give a 5-regular graph of order 5850 at $D=8$.
6. **Formalisation.** Theorem A, Corollary A1 and Proposition C are formal for all odd $q$. Remaining: the Klein correspondence linking Proposition C to Corollary C1, and Theorem B with stand-ins in full.

## References

- [AS69] R. W. Ahrens, G. Szekeres, On a combinatorial generalization of 27 lines associated with a cubic surface, J. Austral. Math. Soc. 10 (1969) 485–492.
- [ADFL21] G. Araujo-Pardo, C. Dalfó, M. A. Fiol, N. López, Bipartite biregular Moore graphs, arXiv:2103.11443.
- [AL20] G. Araujo-Pardo, N. López, On new record graphs close to bipartite Moore graphs, arXiv:2005.02427 (Problem 4: diameters 4 and 6).
- [BGS06] S. Ball, P. Govaerts, L. Storme, On ovoids of parabolic quadrics, Des. Codes Cryptogr. 38 (2006) 131–145.
- [BLP09] J. Bamberg, M. Law, T. Penttila, Tight sets and $m$-ovoids of generalised quadrangles, Combinatorica 29 (2009) 1–17.
- [CDPS22] M. Ceria, J. De Beule, F. Pavese, V. Smaldore, On large partial ovoids of symplectic and Hermitian polar spaces, arXiv:2203.04553, Section 1 (source of the Tallini citations).
- [CCEM08] A. Cossidente, C. Culbert, G. L. Ebert, G. Marino, On $m$-ovoids of $W_3(q)$, Finite Fields Appl. 14 (2008) 76–84.
- [CMPS21] A. Cossidente, G. Marino, F. Pavese, V. Smaldore, On regular systems of finite classical polar spaces, arXiv:2103.09336, Lemma 5.3.
- [D85] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302.
- [DF84] C. Delorme, G. Farhi, Large graphs with given degree and diameter, Part I, IEEE Trans. Comput. C-33 (1984) 857–860.
- [E85] G. L. Ebert, Partitioning projective geometries into caps, Canad. J. Math. 37 (1985) 1163–1175.
- [FLT22] T. Feng, W. Li, R. Tao, On $m$-ovoids of finite classical polar spaces with an irreducible transitive automorphism group, arXiv:2208.13023.
- [FWX19] T. Feng, Y. Wang, Q. Xiang, On $m$-ovoids of symplectic polar spaces, arXiv:1909.07954.
- [P71] S. E. Payne, Nonisomorphic generalized quadrangles, J. Algebra 18 (1971) 201–212.
- [PT] S. E. Payne, J. A. Thas, Finite Generalized Quadrangles, Pitman, 1984; 2nd ed., EMS, 2009.
- [T88] G. Tallini, Fibrations through lines in a nonsingular quadric $Q(4,q)$ of $PG(4,q)$, Atti Accad. Peloritana Pericolanti 66 (1988) 127–146.
- Table of largest known bipartite graphs: F. Comellas, https://web.mat.upc.edu/francesc.comellas/delta-d/ (the copy of [D85] used for the old values: https://web.mat.upc.edu/francesc.comellas/delta-d/papers/81981341.pdf).
