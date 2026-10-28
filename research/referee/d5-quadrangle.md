# Referee report: "Bipartite graphs of diameter 5 from generalized quadrangles: level graphs, surgery and hubs" (D5_QUADRANGLE.md)

Job "referee-d5", 28 October 2026. Document read: research/theorems/D5_QUADRANGLE.md on branch
claude/gq-diameter-5-xa5d3d, head f905b68 (the note last changed in ba1333d; the .tex and .pdf were regenerated in the
same commit and agree with the .md, apart from point 10). Standard: research/referee/d7-2026-10-25.md (branch
claude/referee-d7-hexagon-theorems-hewag2). Prior art was checked against research/lit/novelty-2026-10-25.md (branch
claude/novelty-literature-check-4i5frp), the 2013 survey, Delorme 1985, and an archived copy of the CombinatoricsWiki
bipartite page. My programs and their output are in research/referee/d5_checks/ on this branch (README.md, checks.log).
They share no code with the writer's d5gq/ tools; I used the writer's files only as input data (solution files, the
card c4 example) and to compare edge lists after my own rebuilds.

## Verdict

**The mathematics is sound; the headline is out of date.** I checked every theorem, lemma, proposition and corollary
line by line and found no mathematical error. Every number I recomputed is right. I rebuilt nine graphs with my own code
and checked them with my own all-sources BFS: the (13,5) graph of §11 (11,636), the (15,5)-type graph of §15 (20,713),
and the seven explicit family graphs of §10/§14 built from the printed ingredients alone. All are bipartite, have the
stated maximum degree and diameter 5.

One factual error must be fixed before the note goes anywhere (point 1): the "new record" $n_b(13,5)\ge 11{,}636$ was
overtaken on master about two and a half hours after the note's last commit. Master has had (13,5) = 11,700 (a
multi-doubled-matching lift of $W(8)$) since 26 Oct 09:44 PT. So the note no longer holds the lab's best value in any
cell. What remains, and it is substantial, is the theory (Theorem E, Theorem B with its converse, Theorem C, the
two-point limit of Corollary 6.2, Propositions 7.1–7.2), plus Corollaries 10.1–10.4. Those corollaries beat the 2013 table
in all six cells (10,5)–(15,5) with no computer-found ingredient.

The open prior-art question of §16 can now be closed (point 3): the wiki credits all seven cells (10,5)–(16,5) to
Delorme, Gómez and Quisquater.

Issues: 2 ERRORs (one factual, about the record; one minor, a remark in §12 that no theorem uses), 5 GAPs (2 prior
art, 3 small gaps in statements of §7 and §10), 9 PRESENTATION. Point 6 contains a suggestion that may matter for (15,5): the relaxed-set searches imposed a condition
that the hub rule does not need in the seven-level layout.

## What can be claimed

1. **Theorems with complete proofs** (all checked line by line; the main ones also tested by computer, below):
   Theorem A (the proof; the graphs' orders are the table's, credited to [DGQ]); Lemma 3.2; Theorems 3.5 and 3.6;
   Theorem E (exact criterion for one transition); Theorem B, both directions; Theorem C; Proposition 6.1;
   Corollary 6.2 ($q$ odd: local dualities of $Q(4,q)$ or $W(q)$ on at most two points); Proposition 6.4;
   Proposition 7.1 (the bad pairs of a relaxed set, exactly); Proposition 7.2 (with the hypothesis completed as in
   point 5); Propositions 8.1–8.3; Lemma 9.1; Lemmas 1.1, 1.3, 1.4 (1.1 and 1.4 are standard constructions written
   out); Proposition 2.2; the count of §13.
2. **Lower bounds proved without a computer search** (Corollaries 10.1–10.4 with the hub graphs of Lemma 9.1):
   $n_b(10,5)\ge 4{,}044$, $n_b(11,5)\ge 6{,}090$, $n_b(12,5)\ge 8{,}430$, $n_b(13,5)\ge 11{,}552$,
   $n_b(14,5)\ge 14{,}812$, $n_b(15,5)\ge 20{,}598$. These are 44, 240, 230, 72, 52 and 102 above the 2013 table. They
   are below the lab's values in every cell (4,800; 7,020; 9,840; 11,700; 17,568; 20,736). According to the lab's own
   notes those values come from computer searches (annealed voltages, chart searches); I did not check whether any of
   them has a proof for general $q$.
3. **Computer-checked graphs**: $n_b(13,5)\ge 11{,}636$ and a (15,5) graph on 20,713 vertices. Both are valid and above
   the 2013 table; neither is a record (lab: 11,700 and 20,736).
4. **Do not claim**: a record at (13,5); the base level graphs (the table's cells, credited to [DGQ]); the
   friendly-transition surgery with hubs as such (Rajiv's 2026 preprint has it for general graphs); "the literature
   check found nothing on Theorem E or Corollary 6.2" (it did not search for them; point 4).

**What is new, as far as the sources go.** Nothing in the sources I could read (the survey, Delorme 1985, the wiki
page, the lab's literature check and the papers it read) contains: an exact two-level criterion like Theorem E; the
converse half of Theorem B; local dualities between a quadrangle and itself and the triad argument limiting them to two
points for $q$ odd; relaxed freed sets with the hub rule; or explicit families that beat the 2013 table in these six
cells. The literature check searched for local dualities and relaxed sets only in the hexagon setting, and not at all for
the other three items, so the correct wording is "nothing found in these sources", not "new".

## What I checked by computation

All programs are in research/referee/d5_checks/ (README.md lists them; `run_all.sh` reruns everything into checks.log).

| claim | test | result |
|---|---|---|
| §1.2: coordinates of $W(q)$, $Q(4,q)$; Klein map | $W(q)$ from $w$, and $Q(4,q)$ built **directly** from $X_0X_1+X_2^2+X_3X_4$ (not as $W(q)^D$); GQ axioms; Plücker map line $\mapsto(p_{01},p_{23},p_{02},p_{03},p_{12})$ | axioms hold for $q = 2,3,4,5,7,8,9,11$; the map is an isomorphism $W(q)^D\to Q(4,q)$ for $q = 2,3,4,5,7$; $p_{02}+p_{13} = 0$ on every isotropic line |
| Lemma 1.1 | the $q^2+1$ lines for the first irreducible $X^2-\beta X-\alpha$ | a spread for $q = 2,4,5,7,8,9,11$; the record's ovoid is exactly this spread with $(\alpha,\beta) = (1, x+1)$ in $\mathbb F_9 = \mathbb F_3[x]/(x^2+1)$; the 20,713 graph's with $(1,2)$ in $\mathbb F_{11}$ |
| Lemma 1.2(c) | **all** point triads of $W(q)$, $Q(4,q)$, $q = 3, 5$ | $W(3)$: 1 or 4 centres (2,880 / 360); $Q(4,3)$: 0 or 2 (1,080 / 2,160); $W(5)$: 1 or 6 (312,000 / 13,000); $Q(4,5)$: 0 or 2 (130,000 / 195,000) |
| Lemma 1.3 | the set as printed, random $\tau$, $z$ | $3q-1$ pairwise non-collinear points for $q = 5,7,9,11,13$ (three choices each); the $q=3$ variant has 7 |
| Lemma 1.4 | $\psi$, $\varphi$ as printed | a duality of $W(q)$ for $q = 2,4,8$ (all $N^2$ point–line pairs); $\psi$(spread) is an ovoid |
| §1.3: 18 is the largest partial ovoid of $W(5)$ | max clique among the 100 points non-collinear with a fixed non-collinear pair (PSp(4,q) is transitive on such pairs) | clique number 16, so 18 (and 7 for $W(3)$), agreeing with card r2c8 |
| Theorem E (and Lemma 3.2) | (E2), (E3) evaluated from the statement vs. BFS in the two-level graph, paths with any number of matching edges | agree on 320 random transitions ($q = 2..5$, $W$ and $Q(4,q)$, all four arc types, random/partial-ovoid/pencil/local-duality sets) and on 2,400 perturbed local dualities ($q = 2,3$), among them 6 where only (E2) fails and 105 where only (E3) fails |
| Theorem B | friendly transitions with $M = \mathrm{id}$ | repaired iff partial ovoid/spread in all 83 cases (37 yes, 46 no) |
| Theorem C / Prop. 6.4 | random local dualities built exactly as in Prop. 6.4 | repaired in all 36 two-level tests and on every non-friendly arc of the large graphs below that use them; (H3) checked |
| Computer-checked 6.5 | card c4's $(M,R)$ (only the labelling of $Q(4,5)$ taken from the writer's library, validated by my axiom check) | 3 pairwise non-collinear points, (E2) and (E3) hold, no bad pair in the two-level BFS; triad centres 2 vs 1; (H3) holds at only one of the three points |
| Prop. 7.1 | 18 random relaxed sets, $q = 3,4,5$, $D\to H$, $M = \mathrm{id}$ | the bad-pair set is **exactly** the stated one, $4q$ pairs per partner pair |
| Prop. 7.2 | the same sets plus one $\mathcal A$-hub per partnered line, joined to $(\ell,j')$ and to a point of the partner in level $j$ | 0 bad pairs; with one hub moved off the partner line, $2q-1$ or $2q$ bad pairs remain |
| Props. 8.1–8.3 and the optimum claims of §8 | all 24 (5 levels), all 2,640 (7 levels) and the 46,144 regular tournaments on 9 vertices with $N^+(0) = \{1,\dots,4\}$ (every regular tournament on 9 vertices is isomorphic to one of them), all typings | slot vectors as stated; the maxima of $\min\alpha+\min\beta$ are exactly $2b+2c$, $\min(a+b+4c,3b+3c)$, $4b+4c$ on 969 triples $a\ge b\ge c\ge 0$ |
| Lemma 9.1, card c10's list | feasibility of (Y0)–(Y3) | balanced maxima 15, 45, 120, 255, 468, 780, 1,200, 2,000, 2,925, 4,100 for $\delta = 3..12$ |
| §14 "theorem family" column | best $K_{\mathcal A}+K_{\mathcal B}$ over Lemma 9.1 for each corollary and prime power $q\le 29$ | 4,044; 6,090; 8,430; 11,552; 14,812; 20,598; 26,453, as stated, from the stated $(q,r)$ |
| the seven family graphs | **built from the printed ingredients** (Lemma 1.1 spread carried to my $Q(4,q)$ by the Klein map, Lemma 1.3, Lemma 1.4, Prop. 6.4 with random choices, Lemma 9.1 hub graphs, random hub slots), checked by my BFS | (10,5) 4,044; (11,5) 6,090; (12,5) 8,430; (13,5) 11,552; (14,5) 14,812; (15,5) 20,598; (16,5) 26,453: each bipartite, maximum degree $\Delta$, diameter 5; (10,5) also with a second random seed. Negative control: one extra concurrent line on the $D\to H$ arcs, no hub rule: diameter 6 |
| §11 (13,5) record | rebuilt from the solution file by Definitions 2.1, 3.1 only, with my own $W(9)$ (the file's 820 lines are exactly mine); every hypothesis checked | ovoid = Lemma 1.1; $T$: 66 lines, 30 pairs, no meeting point in $O$; 11 two-point local dualities with (H1), (H3); $\alpha$, $\beta$ as stated; every slot freed and taken once; hub rule 300/300; $Y$-degrees 5 and 6. BFS from every vertex: $n = 11{,}636$, 75,370 edges, simple, bipartite (5,810 + 5,826), degree 10–13, diameter 5. Edge set identical to the writer's .edges.gz |
| §15 (15,5)-type graph | the same for d15D5type_q11_relaxed87_n20713.json | 87 lines, 34 pairs; hub rule 340/340; $n = 20{,}713$, bipartite, degree 12–15, diameter 5 |
| point 6 below ($z\in O$) | seven levels $HHHDHHD$ over $Q(4,q)$, Lemma 1.3 set plus one line meeting a line of it **at an ovoid point**, both hubs of the pair at that point | valid (diameter 5) for $q = 5,7,9$; moving one hub off the partner line gives diameter 6 at $q = 7$ (at $q = 5, 9$ the pair happens to be repaired through other levels, so the rule is sufficient, not necessary) |
| §12, the arc $3\to6$ (point 2) | the 11,636 graph with one more freed element on $3\to6$, three seeds | two-level bad pairs 504, 519, 474; whole graph 440, 438, 403, all between levels 3 and 6 |
| numbers of §§0, 7, 8, 11, 12, 14 | nums.py | all correct (details in "Points checked" below) |

## Issues

### 1. ERROR (factual; record status). §0 "New record", §11, §14 table and text, §16 "The lab's earlier $D = 5$ work"

The note says "**New record.** $n_b(13,5)\ge 11{,}636$ (table 11,480; the lab's previous value 11,486)". That was true
when written (last commit 26 Oct 07:12 PT), but at 09:44 PT the same day the coordinator recorded (13,5) = 11,700
(research/RESULTS.md on master: "(13,5) 11,700 (raised, was 11,486) … all-pairs checked on the Mac mini"; the README
table now lists (13, 5) as 11,700, "lift of a generalized quadrangle"). The graph is the multi-doubled-matching lift of $W(8)$
over $\mathbb Z_2\times\mathbb Z_5$ (branch claude/new-cells-beyond-etos3t, commit 4c61428,
research/frontier/beyond/MDM.md, graphs/d13D5_n11700_W8_2dm_Z10.edges.gz), found by annealing.

*Fix.* Remove "New record" from §0 and the bold from §14; retitle §11 "A (13,5) graph on 11,636 vertices". In §14 put
11,700 in the "lab" column with "multi-doubled-matching lift of $W(8)$". Add (13,5) to the "What does not work" list in
§0. In §16 replace "The previous (13,5) value 11,486 was …" by the current value and its source. The note's headline
should then be the theory and Corollaries 10.1–10.4 (see "What can be claimed").

### 2. ERROR (minor; a remark in §12, no theorem depends on it). §12, last bullet: "pairs between levels 3 and 6 can then not be repaired at all, because every route through a third level uses only friendly arcs"

Routes through *one* other level do use only friendly arcs, and with identity matchings they have length at least
$d+2$, so they cannot help. Routes through *two* other levels can, because they use a non-friendly arc. Example:
$(x,3)\to(x,4)\to(M_{1\to4}^{-1}(x),1)\to(\ell,1)\to(\ell,6)$ has length 4 for every line $\ell$ through
$M_{1\to4}^{-1}(x)$. I tested this on the 11,636 graph. I freed one more random element on the arc $3\to6$, deleted its
matching edge and attached no hub. The two-level graph then has 504, 519 and 474 bad pairs (three seeds). In the whole
graph only 440, 438 and 403 remain, all between levels 3 and 6. So 13–16% of them are repaired through other levels
(arc36.py, checks.log).

*Fix.* "Routes through one other level use only friendly arcs and cannot repair these pairs. Routes through two other
levels repair some of them (about 15% in a test on the 11,636 graph), but not enough, so the later runs keep that arc
fixed."

### 3. GAP (prior art; closes the question left open in §16). §16 first bullet; §0 and §2 where the table is cited

§16 says "We could not open the CombinatoricsWiki page to see whom it credits for these $D = 5$ cells … we assume the
same origin here." I read the page through the Internet Archive (snapshot of 14 January 2025; table "as of January
2012"; its values equal [MS13, Table 4], which the survey itself labels "CombinatoricsWiki, accessed on 10 March 2013").
All seven cells (10,5)–(16,5) are coloured "Graphs found by C. Delorme, J. Gómez, and J. J. Quisquater", reference
"On large bipartite graphs, submitted". Three more facts the note should use:

- (16,5) = 27,300 is also credited to Delorme–Gómez–Quisquater, and it is not of the form $(2r+1)\cdot 2N(q)$ (the level
  graphs give at most 26,352 there). So their paper contains more than these level graphs, and the note can only say
  that the orders of (10,5)–(15,5) coincide with level graphs, not that these are their graphs.
- The page asks to be cited as "E. Loz, H. Pérez-Rosés and G. Pineda-Villavicencio (2010), The degree-diameter problem
  for bipartite graphs, Combinatorics Wiki". The $D = 5$ cells with $\Delta = 5..9$, which §14 compares against, are
  Eyal Loz's voltage lifts from the joint project with Pérez-Rosés and Pineda-Villavicencio (survey §3.4.5, ref. [240]);
  (4,5) is Hafner's and Loz's.
- The survey's own text gives no per-cell credit. It attributes the older bipartite constructions to "Delorme and his
  collaborators … bipartite versions of ∗-product and compounding" ([118, 119]). In §3.3 it describes Gómez, Miller,
  Pérez-Rosés and Pineda-Villavicencio (Networks 53 (2009)), who compound complete graphs into a bipartite Moore
  graph of diameter 6. That is general graphs and hexagons, so it is related to the compounding here but not the same.

I checked Delorme 1985 [De85] myself. §3 is a de Bruijn-type graph on $\mathbb Z/m\mathbb Z\times Q^k$ with duality
adjacencies (general graphs, degree $2(q+1)$), and §6 gives non-bipartite diameter-5 graphs from hexagons. Neither is
the level graph of Theorem A, so "we claim none of these" is accurate. I could not read Delorme–Gómez, "Some new large
compound graphs", European J. Combin. 23 (2002) 539–547, which the wiki lists among its references; someone should look
at it before the note is sent.

*Fix.* Replace the sentence by "The wiki credits the cells (10,5)–(16,5) to Delorme, Gómez and Quisquater [DGQ]; we
could not find that paper. The orders of (10,5)–(15,5) are those of the level graphs of Theorem A; (16,5) = 27,300 is
not of this form." Add [DGQ] and the wiki citation to the references. At Theorem A in §0 and §2, say "these orders are
the table's values, credited to [DGQ]". In §14, credit the $\Delta\le 9$ values to Loz et al.

### 4. GAP (prior art wording). §16 second bullet: "found nothing on: an exact criterion like Theorem E, local dualities (Theorem C) and their two-point limit for $q$ odd (Corollary 6.2), relaxed freed sets with the hub rule (§7)"

The literature check's claim list (1, 2a, 2b, 2c, 3, 4a, 4b, 5) has local dualities (2b) and relaxed sets with
collinear pairs (2c), both searched in the hexagon setting. It has no claim about an exact criterion like Theorem E,
about the converse of Theorem B, or about a limit like Corollary 6.2, so it did not search for them. As written, the
sentence reports a search that was not done.

*Fix.* "The lab's literature check, done for the hexagon case, found nothing on local dualities or on relaxed freed
sets with hub conditions. We did not search the literature for an exact criterion like Theorem E, for the converse in
Theorem B, or for Corollary 6.2." Keep the Rajiv sentence; it is accurate (his Lemma 5 is the "if" half of Theorem B for
friendly transitions, for general graphs).

### 5. GAP (small; statement). Proposition 7.2

The hypothesis speaks of "the $\mathcal A$-hub $g_\ell$ that takes the $\mathcal B$-slot $(\ell,t)$", but Definition 3.1
allows slots that no hub takes ($K_{\mathcal A}\le\min_j\beta_j$). If the slot $(\ell,t)$ or $(m,t)$ is untaken, the two
paths of the proof do not exist and the pairs of Proposition 7.1 can stay bad.

*Fix.* "Suppose that for every line $\ell\in T$ with partner $m$ the $\mathcal B$-slot $(\ell,t)$ is taken by an
$\mathcal A$-hub $g_\ell$ with $\omega'_j(g_\ell)\in m$." In the record this holds: $K_{\mathcal A} = 70$ equals
$\beta_j$ at every $H$ level, and my rebuild found all 300 instances taken and satisfied.

### 6. GAP (small) with a suggestion. §7, paragraph "*The hubs exist.*" and the $W(q)$ reformulation after it

(a) "the rule needs one $\mathcal A$-hub per partnered line and per $D$-level, at most $|T|\le K_{\mathcal A}$ of them".
"Per $D$-level" would mean 120 hubs for the record's 60 partnered lines, more than $K_{\mathcal A} = 70$. In $HHHDHHD$ the
$D\to H$ arcs out of level 3 end in levels 4, 5 and those out of level 6 end in 0, 1, 2. So one $\mathcal A$-hub per
partnered line takes the line's slot on all five arcs, and sits on the partner in both $D$-levels. That is what the
record does (I checked: each of the 60 partnered lines is served by exactly one hub). *Fix:* "one $\mathcal A$-hub per
partnered line suffices when the $D\to H$ arcs out of different $D$-levels end in different levels, as in $HHHDHHD$".

(b) "Distinct partnered lines ask for distinct points … We therefore require $z\notin O$ for every partner pair", and
in $W(q)$ language "the line joining a collinear pair is not in the spread". This condition is not needed in the
seven-level layout. The rule asks only for *some* point of $m$ with a free $\mathcal B$-slot in level $j$. A point of $O$
carries three free $\mathcal B$-slots in level 3 (arcs $0\to3$, $1\to3$, $2\to3$) and two in level 6 ($4\to6$, $5\to6$).
If $z = \ell\cap m\in O$, both $g_\ell$ and $g_m$ can sit at $z$, which lies on both lines. (It can matter when some
$D$-level receives a single $H\to D$ arc, as level 4 in $HHDHD$.) I built such graphs: seven levels over
$Q(4,q)$, the Lemma 1.3 set plus one line meeting one of its lines at an ovoid point, both hubs of that pair at that
point. They are valid for $q = 5, 7, 9$ (z_in_O.py, checks.log).

The searches for relaxed sets imposed the condition: research/theorems/d5gq/relaxed.c, line 2, "every collinear pair of
T is joined by a line NOT in a forbidden line set (the spread S)". §14 says that at $q = 11$ the size of relaxed sets is
exactly what keeps the construction below 20,736 (87 found, 111 needed). So the searches of cards r2c1/r2c2 are worth
re-running without the spread condition (the counting bound 127 does not change). I did not run any search.

*Fix.* State the condition as a convenience, not a requirement, and say when it is needed.

### 7. GAP (small). Proofs of Corollaries 10.2–10.4: "C/Proposition 6.4 (non-friendly arcs)"

Each layout has a $D\to D$ arc ($2\to4$, $3\to6$, $4\to8$), where $M$ maps lines to points. Proposition 6.4 is stated
for $M: P\to L$. The dual statement (non-concurrent lines $x,y$, non-collinear points $\ell,m$) holds by the same proof,
and I used it in my builds, but the corollaries should say so. *Fix:* "Proposition 6.4, and its dual on the $D\to D$
arc".

### 8. PRESENTATION. §0, bullet "Theorems 3.5, 3.6 (assembly)"

The bound $n_b(q+1+r,5)\ge\dots$ also needs the hub graph to have maximum degree $\le q-r$. Add it.

### 9. PRESENTATION. Corollary 10.3 and §0: "$K_{\mathcal B}\le\min(q^2+5,\,6q)$"

For $q\ge5$, $q^2+5-6q = (q-1)(q-5)\ge 0$, so the minimum is always $6q$. Write $K_{\mathcal B}\le 6q$. (In Corollary
10.4 the minimum $\min(q^2+7, 9q-1)$ does switch, between $q = 7$ and $q = 9$.)

### 10. PRESENTATION. The PDF

Lists inside theorem statements are not rendered as lists. Theorem 3.5 reads "Suppose - (T) every transition … and -
(HG) …", and Theorem 3.6, Theorem E ("if and only if - (E2) … ; - (E3) …"), Theorem C ("If - (H1) … - (H3) …") and Lemma
9.1 ("- (Y0) … - (Y1) …") read the same way. In the .md the list starts on the line after the sentence with no blank
line, which pandoc runs together. Insert blank lines and rebuild. Otherwise the PDF (18 pages) renders cleanly and
matches the .md.

### 11. PRESENTATION. Numbering

§6 has Proposition 6.1, Corollary 6.2, Proposition 6.4 and Computer-checked 6.5, with no 6.3. The lettered theorems are
A, B, C, E, with no D. A reader will look for Theorem D; either rename E to D or say once why it is E ("exact").

### 12. PRESENTATION. Lab-internal material in a note "written for Ignacio López and Gabriela Araujo-Pardo"

This is the same point as issue 16 of the D7 report. The note refers throughout to squad cards (c4, c9, c19, r2c1, …),
"the director's annealer", "written by the referee agent" (§14), and "An earlier version of this note … We found this
when a graph violating that condition for 128 slots passed the all-pairs check" (§7). It also lists the record's earlier
versions (11,605, 11,621, 11,626, 11,627). §12 is a lab log. For the version sent out, move these to a lab appendix
or separate file, and keep the *Computer-checked* statements with file paths. The list of earlier versions can go:
11,605 is not explained by the slot formulas (with $b = 51$, $c = 0$ they allow 11,613), and nothing depends on it.

### 13. PRESENTATION. §5, last paragraph: "the graph has diameter 6, as Theorem B predicts for the two levels"

Theorem B predicts that the two-level transition fails. The three-level graph could still have diameter 5 through the
third level (§12 and my point-6 test show this happens). *Fix:* "Theorem B says the transition is not repaired; in this
example the third level does not repair it either: diameter 6."

### 14. PRESENTATION. §12, Heuristic: "about $N/e$ elements of the other level violate (E2)"

For a uniformly random $M$ the expected fraction is $(1-(q+1)/N)^{q(q+1)}$: 0.31, 0.32, 0.33, 0.34 for $q = 5,7,9,11$.
$1/e$ is the limit as $q\to\infty$. Say "about $N/e$ for large $q$". The other numbers of the paragraph (12%, 22%, 330)
follow from the stated formula; I recomputed them.

### 15. PRESENTATION. Header: "the Haiku squad rounds … are in research/squads/gqd5-r1/ and gqd5-r2/"

§7 and §15 also cite research/squads/gqd5-r3/c4/. Add r3. (All cited paths exist on the branch, except
D7_HEXAGON.md and research/lit/novelty-2026-10-25.md, which are on the branches the note names.)

### 16. PRESENTATION (suggestion). Lemma 1.3 and §10

The size $b = 3q-1$ of the explicit partial ovoid bounds $K_{\mathcal A}$ ($\le b+2c$ in Corollary 10.3, $\le b+3c$ in
10.4). This bound, not the hub graph, is what limits the (13,5), (15,5) and (16,5) values of §14 (30, 36 and 38
$\mathcal A$-hubs); at (14,5) the hub graph limits first. For example, an explicit partial ovoid of $W(9)$ with 44 points would raise the hand-proved
(13,5) bound from 11,552 to 11,576 (Lemma 9.1 (Y2) with $s = 3$ then gives $48 + 48$ hubs). Before calling Lemma 1.3 the
best explicit family, it is worth checking the literature on large partial ovoids of $W(3,q)$, $q$ odd (for example the
survey of De Beule, Klein, Metsch and Storme on partial ovoids and spreads of classical polar spaces, and [CDPS], whose
sizes §1.3 says were not compared). The note's own wording ("we did not find it in these sources") is already correct.

## Points I checked and found correct (for the record)

- §0: $N(q) = (q+1)(q^2+1)$. The six table values equal $(2r+1)\cdot2N(q)$ for the stated $(q,r)$, and each is the
  largest value of that form with $q+1+r = \Delta$. (16,5) = 27,300 is not of that form (largest 26,352).
- §1: (F1)–(F4) and their proofs; the Klein correspondence and $p_{02}+p_{13}=0$; the Payne derivative counts ($q^3$
  points, lines of size $q$); Lemma 1.1 (the determinant $\delta_a(\alpha\delta_a+\beta\delta_b)-\delta_b^2$ and the
  case split); Lemma 1.2 (a)–(d) as cited facts (and (c) by exhaustive computation at $q = 3,5$); Lemma 1.3 (every case
  of the proof, including "exactly one of $i = j-1$, $j = i-1$" for $i\ne j$ in $\mathbb Z_3$, and why $q\ge5$ is needed
  for $z$); Lemma 1.4 (polar form in characteristic 2, nucleus $e_2$, the projection).
- §2: Definition 2.1 (bipartite, simple, $(s+1+r)$-regular, order); Theorem A (three cases, lengths 5, 4, 5); Proposition
  2.2.
- §3: Definition 3.1 (slot counts, degrees, order, no multiple edges since a hub has one slot per level); Lemma 3.2 (odd
  number of matching edges; three or more give length $\ge 7$); Definition 3.3; Lemma 3.4; Theorems 3.5 and 3.6.
- §4: Theorem E, all five cases: the parity arguments in (ii), (iv), (v), (iii) from (E2), the equivalence of (iv) with
  (E1), (E2) $\Rightarrow$ (E1) using $R\ne\emptyset$, and that the cases cover all pairs.
- §5: Theorem B, both directions (the line through $y$ other than $xy$ misses $x$ and has $p_\ell = y$), and (E3) $=$
  (E2) for automorphic transitions.
- §6: Theorem C; the remark that (H2) follows ($s+1$ versus $s-1$ common neighbours); Proposition 6.1; Corollary 6.2,
  including the $D\to D$ case; Proposition 6.4 (the four pieces are disjoint, with sizes $2$, $s+1$, $s^2-1$, $s^2-1$).
- §7: Proposition 7.1, all cases (at most two lines of $T$ through a point; $\lambda(v)$; case (iii) via a point
  $w\notin m\smallsetminus\{z\}$); Proposition 7.2, both paths; the counting bound $2(q+1)(q^2+1)/(2q+1)$ = 28, 53, 86,
  127 for $q = 5,7,9,11$.
- §8: Propositions 8.1–8.3 (slot vectors, minima, the condition $b+c\le 2a$, and $K\le a+b+4c$ when $a+c\le 2b$); the
  three-level remark; the $q$ even layout ($\alpha_j = \beta_j = r(q^2+1)$); 2,640 labelled regular tournaments on 7
  vertices.
- §9: Lemma 9.1, all four cases (degrees, pendant counts, the distance arguments).
- §10: Corollaries 10.1–10.4 (the slot bounds $3q+1$; $6q$ and $3q+3$; $\min(q^2+7,9q-1)$ and $3q+5$; the hub degrees
  $q-r$).
- §11: $\alpha = (86,86,86,134,86,86,198)$, $\beta = (70,70,70,246,70,70,166)$, $n = 11{,}480+86+70$; the 21 arcs
  (5 $H\to D$, 5 $D\to H$, 10 $H\to H$, 1 $D\to D$); 300 rule instances; 420 edges of $Y$ with all $\mathcal A$-hubs of
  $Y$-degree 6. The earlier versions 11,621 ($b = 51$), 11,626 ($b = 56$) and 11,627 ($b = 57$) match the slot formulas.
- §12: every level other than 3 and 6 joins them by friendly arcs (true; the conclusion drawn from it is point 2);
  2,184 and 2,236–2,248 vertices; the heuristic's 12%, 22%, 330.
- §13: the $AS(q)$ count ($2q(q+2) < q^3$ iff $q\ge 4$; so $q\ge5$ for $q$ odd), order $4q^2(q+1)$; $GQ(2,4)$: 144.
- §14: the theorem-family column (my optimisation over Lemma 9.1 gives the same $(q,r)$ and hub counts:
  (22,22), (120,120), (120,120), (42,30), (26,26), (66,36), (63,38)); 20,696 ($b = 70$) and 20,713 ($b = 87$); "$b\ge 111$" and
  Tallini's $q^2-q+1 = 111$; 23/28 = 0.82 and $0.82\cdot127\approx104$; "+4 per extra freed point on the ten $H\to H$ arcs";
  $12N(q)$ = 4,800, 7,020, 9,840, 17,568.
- §16 and the references: Rajiv's preprint is described as in the literature check; [GF85], [De85], [MS13], [PT],
  [Ta91], [CDPS] look right as far as I can tell. The note's statements about the D7 note (its Theorem C needed (H2);
  local dualities of 81 to 768 points) are accurate.
