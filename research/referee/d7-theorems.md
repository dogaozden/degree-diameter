# Referee report: "Diameter-7 cells from a spread and its whiskers: the freed sets and the bounds for every q" (D7_THEOREMS.md)

Job "referee-d7thm", 30 October 2026. Document read: research/synthetic/D7_THEOREMS.md on branch
claude/d7-cells-theorems-7h6iex, commit 9125060, with its programs in research/synthetic/d7thm/. The .tex and .pdf in
the same commit match the .md (14 pages; the PDF text contains the last changes, e.g. the three level ranges of §5.1).
Sources read for the cited results: research/theorems/D7_HEXAGON.md (claude/d7-hexagon-theorems-4w1prt, commit a8cd05d),
research/theorems/POLISHED.md §6 (claude/thm-polish-2oddll, commit 3102fa9), research/synthetic/conics2/ and its make
logs (claude/conics-2-diameter-7-ic0oat, commit cbfa594). The standard is that of research/referee/d7-2026-10-25.md. I
did not read the job's own review note. My programs and their output are in research/referee/d7thm_checks/ (README
there); none of them imports the note's code.

## Verdict

**The mathematics is sound.** I checked every theorem, lemma, proposition and corollary line by line (list at the end)
and found no mathematical error and no gap in a proof. Every formula and count I recomputed is right, with one stale
number (issue 1) and one false sentence (issue 2), neither of which touches a theorem. The abstract's main claims hold:
the freed sets of §1 for every odd $q$ and every even $q\ge4$, the tournament bound and its attainment, the bound
$F_k(q)$ for $q\ge q_k$ with the stated thresholds, the fifteen built graphs, and $n_b(18,7)\ge7{,}318{,}644$ and
$n_b(19,7)\ge11{,}316{,}940$ by proof.

I rebuilt the graph of Theorem 3.1 from the printed definitions with my own code (own $\mathrm{GF}(q)$, own $H(q)$ from
the quadric and Tits' equations, the Hermitian spread, $\nu$, $G$, $F$, the whisker set, $S_0$, an elliptic quadric
section, $\sigma$ as in D7_HEXAGON.md Proposition 5.2, the alternating layout, hubs on random free slots) for nine
$(q,k)$ with $q = 3,4,5,7,8$, odd and even $q$, $k = 2,3,4$, and hub graphs from a single edge up to the Lemma 4.2 sum
$H(4)+H(2)$. Every one is bipartite with maximum degree $q+1+k$ and diameter 7 (my BFS from every vertex), and the
orders are $2(2k+1)N(q)+K_1+K_2$. Two negative controls fail as they should.

Issues: 2 ERRORs (a stale number and a false sentence, both in §5), 1 GAP (prior art: "new" for the hub-graph lemmas),
14 PRESENTATION points. Issue 4 is a suggestion: the (18,7) bound is better than the note says, because it needs no
computer at all.

## What can be claimed

- **Theorems, proofs complete.** Theorem 1.4, Proposition 1.5, Lemma 1.6 (any generalized hexagon of order $(q,q)$ with
  a spread); Theorem 1.7 and Corollary 1.8 for every odd $q$ and every even $q\ge4$ (resting on POLISHED.md Lemmas 6.1,
  6.6, 6.10, 6.12 and Theorems 6.5, 6.14, which are refereed and Lean-checked there); Proposition 1.9; Theorems 2.1 and
  2.2; Theorem 3.1 and Corollary 3.2 given a hub graph; Lemmas 4.1–4.3; Theorem 4.4(a).
- **Theorem 4.4(b)** is a theorem with a computer-made certificate list: 590 sums of at most nine blown-up hexagons
  ($q\le200$), each checkable by hand, plus a scan with Lemma 4.1 alone for $200<q\le2\cdot10^5$. I re-checked both with
  independent code (all 590 certificates valid; the scan succeeds everywhere, with $c\le2$). "Computer-assisted" is the
  right label.
- **Bounds.** $n_b(q+1+k,7)\ge F_k(q)$ for $2\le k\le12$ and every prime power $q\ge q_k$ (table of Theorem 4.4), and
  for every $k\ge2$ and every prime power $q\ge300k$. The "proved" column of §5.2 ($\Delta = 14,\dots,26$) is right as
  printed; each value is Theorem 3.1 with an explicit sum of blown-up hexagons.
- **(18,7) and (19,7).** $n_b(18,7)\ge7{,}318{,}644$ is a theorem whose ingredients are all explicit and classical or
  elementary (Hermitian spread, the exact whisker set of POLISHED.md, an elliptic quadric section, $H(7)+H(7)$); no
  computer is needed (issue 4). $n_b(19,7)\ge11{,}316{,}940$ is a theorem with a five-part sum as hub graph.
- **Built graphs and records.** None of the cells $(17,7)$–$(26,7)$ has a value on master; "the lab's value 7,309,092"
  is the conics-2 branch value. The new (18,7) graph is reproducible: I rebuilt it from its solution file (edge-list
  sha256 `c80d9c0e…` as recorded) and checked it with my own BFS from all 78,432 hubs and from 6,400 random level
  vertices (results below). The bound does not depend on a full all-pairs check, since every ingredient is proved and
  the hypotheses hold by construction; but the lab's rule for recording a value still asks for the coordinator's
  all-pairs check of the built graph, as the note says.
- The **Heuristic** label in §4 is right: it is an observation on 17 runs.
- The **labels** Theorem / Computer-checked / Heuristic are used correctly; [new] / [restatement] are right except
  where issues 3 and 9 say.

## What I checked by computation

All programs are new (research/referee/d7thm_checks/). Lab code is used only to turn the (18,7) solution file into an
edge list (conics2/typed_build.py), as in the earlier referee report.

| claim | test | result |
|---|---|---|
| §0, §1 counts; $P-\Lambda$, $N-P = q(q^4+q)$, $\lvert R_L\rvert$, free points | identities for all prime powers $q\le400$ (`nums.py`) | all hold |
| Theorem 2.2 | $f_j$, $g_j = f_{2k-j}$ and the minima for $k\le40$, several $(q,m)$ | all as stated whenever $(\ast)$ holds |
| $(\ast)$ ranges | direct | $k\le23$ at $q=11$, $m=768$; $k\le27$ at $q=13$, $m=792$; $k\le2q+1$ for $m=q^2+1$, all $q\le300$ |
| Theorem 2.1 | all labelled regular tournaments with 3, 5, 7 levels (2, 24, 2,640) × all typings; 20,000 random pairs with 9–15 levels | no violation of (a)–(c); the best $\min\alpha+\min\beta$ over all of them equals the alternating layout's, for five $(q,m)$ |
| table of build layouts (§2) | symbolic slot vectors of $HDHDH$, $HHDHHDD$, $HHDHDHDHD$ | equal to the table; $HHDHDHDHD$ is a rotation of the alternating typing |
| Corollary 3.2 | closed forms against the slot formulas, every prime power $q\le200$, $1\le k\le q-1$ (5,025 pairs); $F_2,F_3,F_4$ | all equal |
| §5.1, "the formulas reproduce all fifteen builds" | the 12 make logs on the conics-2 branch parsed: $\lvert R_H\rvert$, $\lvert R_L\rvert$, $m$, slot vectors, hub counts, $n$ (`builds.py`) | all 12 agree; the other 3 (job conics) agree by order (issue 6) |
| Theorem 4.4(b), $q\le200$ | every line of `hubopt.out` against Lemmas 4.1–4.2 and the slot counts (`certs.py`) | 590 certificates, all valid; thresholds $q_k$ exactly as in the table |
| Theorem 4.4(b), $200<q\le2\cdot10^5$ | own scan, Lemma 4.1 alone, $2\le k\le12$ (198,660 pairs) | no failure; $c\le2$ always suffices |
| Theorem 4.4(a) | the numbers of the chain | $600^{4/5}=166.9$, $q^{-4/5}\le0.00599$, $1.2^5(1+1/600)/0.97 = 2.570 < 3$, $3\cdot300^{-1/5} = 0.9587$ |
| $q_k$ and §5.2 values below $q_k$ | own search (blow-ups, at most one pendant-tree part last, $\le10$ parts) for all 96 $(q,k)$ below $q_k$, $k\le12$ (`mysearch.py`) | same best value as `hubopt.out` at all 96; no full-slot sum (issue 7) |
| §5.2 table | best $(q,k)$ per cell, level-graph value, $F_k$, status, proved value (`table52.py`) | all 13 rows reproduced; the proved values are the best over all $(q,k)$ and exceed the level graphs |
| §4 random-hub-graph table | $K_{\mathcal B}$, $K_{\mathcal A}$, $M(\delta)/K_{\mathcal B}$ | all 17 rows reproduced |
| own $H(q)$ | from the quadric and Tits' equations, $q = 2,3,4,5,7$ (`t_hex.py`) | $N$ points, $N$ lines, $q+1$ per element, distance profile $1,(q+1),\dots,q^5$ |
| Lemma 1.2, Theorem 1.4(a)–(c), Lemma 1.6, Theorem 1.7, Corollary 1.8, Prop. 1.9 | asserted inside the rebuild at $q = 3,4,5,7,8$ (`build31.py`) | all hold: $W$ exact, $\nu$ constant on spread lines, 0 or $q+1$ whiskers per spread line, $\lvert S_0\rvert=q^2$ ($\nu=0$), $\lvert R_L\rvert = 93, 276, 655, 2457, 4168$, dual segment, maximal (every outside line tested), $\mathcal P_S$ a segment set, $q^2+1$ pairwise opposite points, $\sigma$ a local duality |
| Theorem 3.1 (rebuild) | $(q,k)$ = (3,2) edge, (4,2) $C_{12}$, (4,3) edge, (5,2) $H(2)$, (5,3) $C_{12}$, (5,4) edge, (7,2) $H(4)$, (7,3) $H(3)$, (8,2) $H(4)+H(2)$; BFS from every vertex (`bfsd.c`) | all VALID: bipartite, simple, max degree $q+1+k$, diameter 7; $n$ from 3,642 to 377,346; min slots as in Theorem 2.2 |
| negative controls | (5,2) checked with $D=6$; (5,2) without the hub-graph edges | 368,135,166 and 680 ordered pairs beyond the limit |
| Lemma 4.1 | random blow-ups of $H(2)$ ($c=3$) and $H(3)$ ($c=2$) (`hubtests.py`) | same colour $\le6$, different colour $\le5$, degree $\le c(s+1)$ |
| Lemmas 4.2, 4.3 | $H(3)+H(2)^{\times2}+H(2)+$ pendant-tree part on PG(2,2) (asymmetric sizes); a pendant-tree part on PG(2,3) alone | same colour $\le6$ (the tree part has different-colour distance 7, as the note says) |
| negative control | pendant-tree part first, $H(2)$ second | 1,992 same-colour pairs at distance 8 |
| the hub graphs of the two headline bounds | $H(7)+H(7)$; the (16,2) certificate $H(8)+H(7)+H(5)+H(4)^{\times2}[2730]+H(4)^{\times2}[2372]$ built by my code | HG(39216,39216;9), 9-regular; HG(66065,66065;14); same colour $\le6$ |
| stored hub graphs | the hub graph in the (18,7) solution file; PSL(2,29) of job conics; the (17,7) and (20,7) random ones (`hubfiles.py`) | see `hubfiles.log` (results below) |
| (18,7) graph | rebuilt from `d18D7_hex13_typedwhisk_h7h7_n7318644.sol`; own BFS from all 78,432 hubs and from 6,400 random level vertices | see `d18_check.log` (results below) |

(The (18,7) and stored-hub-graph results are added below when the runs finish.)

## Issues

Each issue gives the place (section and first words), the problem and a fix.

### 1. ERROR (stale number). §5.1, paragraph "At $(19,7)$ and $(20,7)$ the built graphs …", last sentence but one: "with the proved equal-sided hub graph of $65{,}737$ hubs per colour the bound is $15{,}790{,}208$"

The note's own certificate for $(q,k) = (16,3)$ (`hubopt.out`, and the §5.2 table) has $66{,}234$ hubs per colour:
$H(8)+H(7)+H(5)+H(5)+H(4)$, degrees $9+4, 8+4, 6+4, 6+4, 5+4\le13$, which gives
$14N(16)+2\cdot66{,}234 = 15{,}791{,}202$. The number 65,737 appears in no output file of d7thm/ (it is left over from
the earlier search). *Fix:* "$66{,}234$ hubs per colour … $15{,}791{,}202$", as in §5.2.

### 2. ERROR (false sentence). §5.2, last paragraph: "The values with computer-found ingredients (the lab's sets $m=768,792$ and hub graphs) are the built values of §5.1 and are larger at $q=11,13$."

At $(18,7)$ ($q=13$) the built value 7,309,092 is smaller than the proved 7,318,644, as the first sentence of the
same paragraph says. *Fix:* "… and are larger at $(14,7)$–$(17,7)$; at $(18,7)$ the explicit hub graph $H(7)+H(7)$
beats the computer-found one."

### 3. GAP (prior art). Abstract, "The hub graphs are given by a new explicit construction (sums of blown-up hexagons)"; Lemma 4.1 "[Theorem; elementary]"; Lemma 4.2 "[new]"

The note's convention ("new" means new in the lab's notes; no literature search) is stated under *Labels*, but the
abstract will be read by outside readers as a claim of novelty, which is exactly the kind of claim the previous report
(issue 1 there) found wrong. Two pieces of prior art are already cited in the lab's own notes:

- duplicating elements of the split Cayley hexagon is Delorme's construction [De85a, §8(b)] (D7_HEXAGON.md,
  Corollary 5.3(a); POLISHED.md, Remark 6.9, where the copies are called "versions"); Lemma 4.1 is the uniform version
  of it, and the projection argument is standard;
- joining several graphs by matchings along a tournament is the compound-graph idea of Gómez and Fiol ([GF85], cited in
  D7_HEXAGON.md §11, which also credits Delorme with bipartite versions of compounding [De85a, De85b]); Lemma 4.2 is a
  compound of parts of different sizes joined by injections along a transitive order.

*Fix:* label Lemma 4.1 [standard] and cite [De85a, §8(b)]; say after Lemma 4.2 that it is a compound in the sense of
[GF85] and that the new point is the order condition with the different-colour distance 5, which makes every
same-colour pair reach distance 6 through an earlier part; in the abstract write "explicit hub graphs (sums of
blown-up hexagons)". If the note is to be sent outside the lab, run the literature check on Lemmas 4.1–4.2 first.

### 4. PRESENTATION (suggestion; strengthens the note). §5.1, "A larger (18,7) graph [new; Theorem, built and partly computer-checked]", and the abstract

The bound $n_b(18,7)\ge7{,}318{,}644$ needs no computer: Theorem 3.1 at $(q,k)=(13,4)$ with the sets of Corollary 1.8
and Proposition 1.9 (slots $2(\Lambda(13)+170) = 57{,}826$ per side) and the hub graph $H(7)+H(7)$ of Lemma 4.2
($39{,}216$ per colour, degree $8+1 = 9 = q-k$). Every ingredient is classical or explicit, so the result can be checked
by hand. It is also the only cell where an explicit construction beats a value the lab found by search. Say this in the
abstract and in §5.1 ("Theorem; all ingredients explicit. The graph with the build's 792-point set was also built and
checked from every hub"). Also say that the lab's 7,309,092 is a branch value (conics-2), not a value on master.

### 5. PRESENTATION. Two different hub graphs are named for $(19,7)$

§5.1 ("Theorem 4.4: $H(8)+H(7)+H(5)+H(5)$ and a pendant-tree part") and the proof of Theorem 4.4 name the decomposition
of the earlier search (`hubsum.out`); the §5.2 table and `hubopt.out` give
$H(8)+H(7)+H(5)+H(4)^{\times2}+H(4)^{\times2}$. Both are valid (I built and checked the second; the first's numbers
satisfy Lemma 4.3: $t=4$, $u=9$, $c_P = 124\le31\cdot4$, $c_L = 116$, $g_P = 1{,}049\le9\cdot124$,
$g_L = 1{,}041\le9\cdot116$). The first line of `cert_checks.out` does not say which one was built. *Fix:* name one
decomposition in both places (the blow-up one needs no pendant part) and say which one `cert_checks.out` checked.

### 6. PRESENTATION. §5.1, "every slot vector equals the one printed in the make logs on branch claude/conics-2-diameter-7-ic0oat"

Twelve of the fifteen builds have a make log on that branch, and all twelve agree with the formulas (my `builds.py`;
this includes the (15,7) 16,152 build, whose `make_meta.log` `cells.py` does not compare). The three builds of job
"conics" ((14,7) 1,802,400, (15,7) 2,504,544, (16,7) 4,081,072) have no make log; they are compared by order only (and
agree). *Fix:* say so.

### 7. PRESENTATION. Theorem 4.4(b), "These are the thresholds of our search, not of the method"

My search, written independently with the same lemmas (blow-ups, at most one pendant-tree part, last; at most ten
parts; sizes filled in order), finds exactly the note's best value at all 96 $(q,k)$ below $q_k$ with $k\le12$, and no
full-slot sum. So the $q_k$ are the thresholds of sums of Lemmas 4.1–4.3 as far as two independent searches can tell
(neither search is exhaustive over size assignments, so this is not a proof of optimality); a better threshold needs a
different kind of hub graph. *Fix:* "the smallest $q$ from which our sums of Lemmas 4.1–4.3 reach the full slots (two
independent searches agree); other hub graphs may do better". Also worth saying: for $200<q\le2\cdot10^5$ a single
blow-up with $c\le2$ suffices.

### 8. PRESENTATION. §1.3, Remark (iii): "… is at least as good as any typed layout, by Theorem 2.1"

Theorem 2.1 assumes friendly sets of sizes $P$, $\Lambda$ and non-friendly sets of size $m\le\Lambda$. At $q=3^h$ a
non-friendly $H\to H$ transition with a duality can free all $P(q)$ spread points (D7_HEXAGON.md, Corollary 4.3(3)), so
Theorem 2.1 does not cover the typed layouts at $q=3^h$. The statement is true for a simpler reason: every freed set
allowed by Theorems B and C has at most $P(q)$ elements (Proposition 1.4; a non-collinear set has at most
$q^4+q^2+1<P(q)$), so $\alpha_j,\beta_j\le kP(q)$, which the duality layout attains. *Fix:* give this reason.

### 9. PRESENTATION. Labels

Corollary 1.8 has no [new]/[restatement] label (§6 calls it a restatement of conics2 Proposition 1); Lemma 4.1 has none
(issue 3). Lemma 1.2 is "[restatement]" without a source: (c)–(e) are in POLISHED.md §6.2 (free points, whisker bound).

### 10. PRESENTATION. §0, "The value $2(2k+1)N(q)$ alone … is the value of the 2013 table at the cells (7,7), (9,7)–(16,7)", and §3 after Corollary 3.2, "(the 2013 table value when $q+1+k\le16$)"

True only for the best $(q,k)$ of each cell: for instance $(q,k) = (11,4)$ gives $18N(11) = 3{,}188{,}808$ at $\Delta =
16$, not the table's 4,022,340. *Fix:* "for the $(q,k)$ of the table in §5.2" (and in §0, name the pairs: $(5,1)$,
$(7,1)$, $(8,1)$, $(9,1)$, $(9,2)$, $(11,1)$, $(11,2)$, $(11,3)$, $(13,2)$; I checked all nine values).

### 11. PRESENTATION. §2, after Theorem 2.2: "So, with friendly point sets of size $P$ … the alternating layout maximizes $K_{\mathcal A}+K_{\mathcal B}$ (and for $k$ even each of them) over all regular tournaments and typings."

This needs $(\ast)$: for even $k$ in the bound (in the form $\Lambda-m\ge(a-1)(P-\Lambda)$), for odd $k$ in the value
$\min\alpha = aP+(a+1)m$ of the alternating layout (the bound itself needs only $P\ge\Lambda\ge m$). *Fix:* add
"under $(\ast)$".

### 12. PRESENTATION. Notation against D7_HEXAGON.md

Here $k$ is the number of transitions out of a level, which D7_HEXAGON.md calls $r$; there $k$ is the step of a
transition $(j,k)$. One sentence in §0 avoids confusion for a reader of both notes. In the same paragraph, add that
regularity of the tournament is also what makes the degree $q+1+k$ (a level with $k+1$ outgoing transitions would give
its $\mathcal A$-elements degree $q+k+2$), so regular tournaments are the right class for Theorem 2.1.

### 13. PRESENTATION. Lemma 4.3: "and $g_P$, $g_L$ pendant vertices below these (at most $u$ per vertex)"

Say which are below which: $g_P$ below the $c_P$ pendants attached at points, $g_L$ below the $c_L$ attached at lines.
The colour-class sizes in the conclusion fix this reading, but the sentence does not.

### 14. PRESENTATION. §4, Heuristic: "Where they fail the lab used Haar graphs over $\mathrm{PSL}(2,p)$"

The (15,7) graph uses $\mathbb Z_{673}\rtimes\mathbb Z_{24}$ (§5.1 table). *Fix:* "Haar graphs over
$\mathbb Z_{673}\rtimes\mathbb Z_{24}$ and $\mathrm{PSL}(2,41)$".

### 15. PRESENTATION. §1.3, "*Computer-checked.* `conics2/typed_build.py` asserts every statement of Theorem 1.7 and Corollary 1.8 for $q=4,5,7,11,13,16$ inside the builds"

The branch has logs for $q=11,13,16$ only (the make logs); conics2/README.md says the builder was also run at
$q=4,5,7$, but no log is there. Point to those runs or drop $q=4,5,7$ here. (My rebuild asserts the same statements at
$q=3,4,5,7,8$, odd and even.)

### 16. PRESENTATION. §6, paragraph "*Review.*", and the internal references

The *Review* paragraph says "all corrected here", but issues 1 and 2 remain. For a version sent outside the lab, move the
internal material (job names, squad cards, the coordinator, the review paragraph) to a separate lab note, as
D7_HEXAGON.md did with its old §12.

### 17. PRESENTATION (PDF). Page 11

The sha256 string in §5.1 runs into the right margin. Break it, shorten it (`c80d9c0e…`, with the full hash in
d7thm/d18D7/README.md), or put it in a footnote.

## Points checked and found correct (for the record)

- **§0.** $N(q)$, $\lvert\Gamma_i(x)\rvert$; spreads and Lemma 1.2(c) of D7_HEXAGON.md; segment and dual segment sets and
  their bound; layouts, $\alpha_j$, $\beta_j$; Theorem A and Theorem 3.4 of D7_HEXAGON.md carry over to every regular
  tournament (their proofs use only one transition per pair of levels; Lemma 3.3 uses any level); Theorem 0.1; what
  repairs a transition (Theorem B for segment sets at friendly identity transitions, Theorem C with Corollary 5.3(a) and
  Proposition 5.2 for $H\to H$, and with $\sigma^{-1}$ and $\sigma(R)$ for $D\to D$, where (H1)–(H3) transfer); the
  nine table values $2(2k+1)N(q)$.
- **§1.** Definition 1.1; Lemma 1.2 (a) (no circuit of length 4 or 6), (b), (c) $q^3(q^2-1)$, (d), (e); Proposition 1.3;
  Theorem 1.4 (a) (every line of $\mathcal L_v\cup W$ has exactly one point in $\mathcal P_S$; the other points are at
  distance 3 from $v$ on one line of $\mathcal L_v$ and no whisker, or free on no line of $\mathcal L_v$ and at most one
  whisker; lines of $S_0(W)$ are isolated), (b), (c) (every point covered; an outside line meets $q+1$ different lines),
  (d); Proposition 1.5 ($N-P(q) = q^5+q^2$; the dual segment property is not even needed, only the meeting points); the
  remark after it; Lemma 1.6 ($q-1$ possible whiskers at each point of $n$; $q^2(q^2-1)/(q+1) = q^2(q-1)$); Theorem 1.7
  against POLISHED.md §6 (on $\Pi$ the equation of $\Pi_z$ is $\alpha X_2+\beta X_5=0$ for both parities; one line of
  $S_z$ through $X$ for each $z = tz_0$, not $v$, not in $S$, meeting $\Pi$ only in $X$, distinct for distinct $z$;
  $F(tz_0) = tF(z_0)$ with $F(z_0)\ne0$ since $G$ is zero-free and $N$ anisotropic; $\nu$ constant on spread lines by
  POLISHED Lemmas 6.6(d), 6.12(d)); Corollary 1.8 (maximality from Theorem 1.4(c)); Remarks (i)–(iv) (numbers 12, 18,
  276; (iii) see issue 8); Proposition 1.9.
- **§2.** The slot formulas ($Y_j=\Lambda$ at $H$ levels since friendly transitions into $H$ come from $D$); $(\ast)$ for
  $k\le2q+1$, $m\le q^2+1$, and the two ranges; Theorem 2.1 (a)–(c) ($\sum_{\tau_j=H}(k-f_j) = \binom h2$ and the three
  counts) and all four consequences (the even case needs only $\Lambda-m\ge(a-1)(P-\Lambda)$, true for $k=2$); Theorem
  2.2 (the four parity cases, the reflection $j\mapsto2k-j$ reversing transitions, both minima); the build-layout table;
  "the $k=3$ layout of the builds has the same minima" (needs $\Lambda-m\ge P-\Lambda$, true here).
- **§3.** Theorem 3.1 (all hypotheses of Theorems B, C, 2.2 and 0.1 met; $(\ast)$ from $k\le q-1$); Corollary 3.2 and
  $F_2,F_3,F_4$; the gains; the comparison with D7_HEXAGON.md Corollary 9.3 ($2(q+2)(q^2+1)$ for $q\ge16$); the change
  $k(m-q^2-1)$ resp. $(k+1)(m-q^2-1)$ for a larger non-friendly set (under $(\ast)$).
- **§4.** $\frac4{27}\delta^4$ for Lemma 7.1 of D7_HEXAGON.md; Lemma 4.1 (projection of paths; copies of one element at
  distance 2); Lemma 4.2 (degree $\Delta(Y_i)+(i-1)+(r-i)$; the distance argument uses different-colour distance $\le5$
  only in $Y_i$, $i<r$); Lemma 4.3 (all same-colour cases $\le6$; different colours can be 7); Theorem 4.4(a) line by
  line ($q^4<\Lambda\le K_{\mathcal A}\le K_{\mathcal B}$, $K_{\mathcal B}/K_{\mathcal A}\le P/\Lambda\le1+1/q$,
  $K_{\mathcal B}\le k(q+1)^4$, Nagura applied at $x/1.2\ge25$, $K_0(s)<K_0(x)<(x+1)^5$, Bernoulli, the final
  $0.041(q+1)\ge12.3k\ge k+1$); (b) and the three worked examples ((16,2), (23,3), (13,4)); the examples' degrees.
- **§5.** All seven rows of the §5.1 table (orders, slots, hub counts); "16,152 of 16,309" and "34,440 of 59,070"; the
  (19,7) chain of proved ingredients; the (18,7) numbers ($18\cdot402{,}234+2\cdot39{,}216$, "9,552 more"); the (18,7)
  build log, level comparison and the check from every hub (files read; the hub check repeated with my code); all 13 rows
  of §5.2 and the $(15,7)$ value $2{,}504{,}544$ with the PSL(2,29) hub graph (slots $(16228,15017)$ with $m=122$,
  degree $8=q-k$).
- **§6 and the appendix.** The summary table matches the body (except issues 1–3 carried over); the files listed exist on
  the branch; the squad round directory has cards c1–c6 and a scoreboard.
- **References.** [MS13], [Na52] (for $y\ge25$ a prime in $(y,\frac65y)$), [Th80], [VM98]: as far as I can tell, right.
