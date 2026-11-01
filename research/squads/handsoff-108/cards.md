# handsoff-108: direction cards (round 1, 2026-10-31)

Goal for every card: a bipartite graph with max degree 10, diameter 8 and MORE than 1,176,480 vertices (cell Δ10·D8).
For a Haar graph H(G,S) that means |G| = N ≥ 588,241 and |S| = 10. Background (read the first 120 lines, then
search it when needed): `research/squads/cells/d10D8.md`. Tools: `research/d10D8/README.md`.

## Common rules (all workers)

- Repo: /home/user/degree-diameter. Work ONLY inside your folder `research/squads/handsoff-108/<worker>/` (copy tools
  there if you change them). Read-only everywhere else. No git commands that change anything (no commit, checkout,
  stash, reset). Reading other branches is fine: `git show origin/<branch>:<path>`.
- Machine: 4 cores and 15 GB shared by 8 workers and the coordinator. At most ONE heavy process at a time (the grind
  card: two), always `nice -n 10` (grind: `nice -n 15`), `THREADS=1`, at most 1.5 GB of memory, and a `timeout` on
  every run. Start long runs with `nohup ... &` and write their logs into your folder.
- Bash calls end after 10 minutes. To wait for a run, poll in a loop, e.g.
  `for i in $(seq 55); do sleep 10; done; tail -3 run.log`. Never print a big file; use tail, grep, wc.
- Scorer: `research/d10D8/sym2/haar_sym2` (built; usage in its header and in `research/d10D8/README.md`).
  Cost = uncovered group elements (with ORBW=3 an uncovered α-fixed element weighs 3). Cost 0 = diameter 8.
  It prints `RESULT ... best=C` and, with RESTARTAFTER=0, one `CHAIN n min C ... S <10 element indices>` line per
  fresh descent. A run that reaches cost 0 writes the solution file itself (after its own full check).
- If anything reaches cost 0: copy the solution file to `research/squads/handsoff-108/records/`, run
  `research/squads/handsoff-108/shared/check.sh <that file>` once, add a scoreboard line with note `CLAIM`, and
  keep going. The coordinator verifies.
- Scoreboard: append ONE line per real improvement (your first result, then each new best) to
  `research/squads/handsoff-108/scoreboard.tsv`, tab-separated:
  `time_utc  worker  strategy  vertices_2N  cost  file  note` (use `printf '...\t...\n' >> scoreboard.tsv`).
  `file` = the log or set file that holds the evidence. Keep the note short; say the units (plain or ORBW=3).
- Notes: keep `research/squads/handsoff-108/<worker>/NOTES.md` up to date (what you ran, numbers, what you learned,
  what you would try next). Write plainly, short lines.
- Mandate: work autonomously for about 2 hours. Do not report back early, do not ask questions. When one idea
  is done or dead, write it down and start the next variant yourself. Before you finish: stop your processes
  (the grind card leaves its two runs alive and says so), update NOTES.md, and reply in at most 6 lines.
- Fresh seeds only: your seed range is on your card. Seeds 1-62, 1001-1008, 2001-2008, ..., 8001-8008 are used.

Reference numbers (psl 23 97 = PSL(2,23) x Z97, N = 588,984; prod = PSL(2,7) x SL(2,8) x Z7, N = 592,704;
ORBIT="3 3 1", F15W3 = `RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`):
RANDORB (random symmetric S) on psl 23 97: min 36, p1 52, p10 84, median 135. Fresh F15W3 descents (about 50 s
each on a free core): chain minima median 18-21; P(min ≤ 9) ≈ 1 in 15; about 14,000 descents so far, lowest 3
(twice: one uncovered α-fixed element), no cost 0. Speed: about 2,500 evaluations/s on a free core.

---

## c1-grind: volume on the two known-good groups (2 processes)

Run fresh F15W3 descents, one process per group, at `nice -n 15` (lowest priority: you soak up idle cycles):
`cd research/squads/handsoff-108/c1-grind && ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 CKPT=g1.ckpt
nohup nice -n 15 timeout 25000 /home/user/degree-diameter/research/d10D8/sym2/haar_sym2 10 8 24000 108101 8 g1.txt psl 23 97 > g1.out 2>> g1.log &`
and the same with seed 108201, tag g2, group `prod psl 7 sl 8 7`. Seeds 108101-108199 / 108201-108299 if you
restart. Every 10-20 minutes: count CHAIN lines, update a histogram of chain minima in NOTES.md, add a scoreboard
line for any chain min ≤ 6. If a chain reaches energy ≤ 3, take its S and run `EXDESC=1` on it (read the README:
`CKPT=<file with that set>`), in your folder, to see if one orbit swap finishes it. Extra (when idle): fit the tail
of the chain-minimum distribution (all your CHAIN lines plus `research/squads/handsoff-108/shared/good_states.tsv`
for the old low ones) and estimate P(cost 0) per descent. Seeds: 108101-108299.

## c2-repair: two-orbit moves from the 119 best known states

`shared/good_states.tsv` holds 119 states (energy 3, 6, 9; ORBW=3 units) found by earlier grinds; every one tested
so far is an exact local optimum under replacing ONE orbit (EXDESC=1). Try moves that change TWO things at once:
(a) for each pair of slots (i, j), take the top-K single-slot replacements of slot i and of slot j (ranked by cost,
from a NEIGH/EXDESC-style scan; K ≈ 100-300) and evaluate all K×K pairs; (b) replace the fixed letter e by another
α-fixed element together with one orbit; (c) right-multiply two orbits by the same α-fixed element c (α(x c) =
α(x) c keeps the symmetry). Start with the two energy-3 states. You will need a small driver that evaluates a given
list of S quickly; extend a copy of `research/d10D8/sym2/haar_sym2.c` or `research/d10D8/zopt/haar_zopt.c` (it
already has NEIGH=K and a fixed-set mode via CKPT=). Report the best energy reached and whether 2-moves ever beat
the start. Seeds: 108301-108399.

## c3-twist: cut the abelian tax with a twisted cyclic factor

In Q × Z_n with orbit-symmetric S, a word's Z-part is c(w)·z with c(w) depending only on the letter pattern, so many
words collide for every z (cell notes §5: 6-23 % of words lost). haar_sym2 also supports two non-direct groups
(whole group only): `tpgl q` = Z_n ⋊ PGL(2,q) (PGL acts on Z_n by the sign of det being a square or not) and
`csl q` = (SL(2,q) × Z_n)/⟨(−I, n/2)⟩ (n even). In tpgl the Z-part of a word gets signs that depend on the
Q-path, which should break the collisions. Candidates with N in the window (check orders yourself): tpgl 23 n 49
(595,056), csl 23 n 98 (595,056), tpgl 13 n 271 (591,864); find more (n should have every prime ≡ 1 mod 3 if α acts
on Z_n, otherwise Fix(α) grows). Steps: RANDORB=1000 on each (compare min/p1/p10/median with psl 23 97 above,
but note μ is bigger for bigger N: μ = N·exp(−5,380,840/N)); measure the duplicate-word rate if you can; then run
F15W3 descents on the best one or two for at least 40 minutes each and compare chain-minimum distributions with
psl 23 97 (median 18-21, 1 in 15 ≤ 9). Seeds: 108401-108499.

## c4-groups: screen every direct-product group in the window

`research/structured/tools/orb_screen.py` lists groups Q × Z_n for ORBIT k m f (run it with no args or read its
header for usage; e.g. d=10, D=8, range 588241 600000, kmf "3 3 1"). Measured so far: psl 23 97, prod psl 7 sl 8 7,
prod psl 5 psl 27 (n = 1), psl 17 241, prod sl 3 sl 7 73 (cell notes §4, §5, §7: the tight psl 23 97 and prod are
best). Screen everything else haar_sym2 can build in 588,241-600,000 (sl/psl/pgl, prod of two, agl1, meta, × Z_n),
RANDORB=1000 each (`RANDORB=1000 ORBIT="3 3 1" ORBW=3 ...`), rank by p1 and median adjusted for μ. Then F15W3
descents (≥ 30 min) on the top 2-3 new groups. A group whose descents reach ≤ 9 more often than 1 in 15 is a find.
Seeds: 108501-108599.

## c5-selfdual: twisted pairing S⁻¹ = β(S) with an order-3 symmetry (ψ of order 6)

If S⁻¹ = β(S) for an involutory automorphism β, the odd words are closed under x ↦ β(x)⁻¹, so uncovered elements
come in pairs; with α of order 3 normalised by β, in orbits of 6 (μ_A ≈ μ/6 ≈ 10.6 instead of 21). Earlier test
(cell notes §8.4, `INVPAIR=2` in haar_sym2, β outer on PSL(2,7) inside prod psl 7 sl 8 7): 1,792 ι-fixed elements
(x with β(x) = x⁻¹, each costs e^(−λ/2)) and a tiny orbit space sank it. Your job: the same family on psl q × Z_n
(e.g. psl 23 97) with β = (conjugation by an OUTER involution b of PGL(2,q) that inverts the α-element a) × (z ↦ z):
then ι-fixed elements need z = 0, only about q²/2 of them. S = {e} ∪ O ∪ ι(O) ∪ (α-orbit of ι-fixed elements),
ι(x) = β(x)⁻¹. The family is small (≈ N/3 × #ι-fixed orbits ≈ 10⁷-10⁸), so after RANDORB you can enumerate it
exhaustively. Copy haar_sym2.c and extend INVPAIR=2 to psl groups, or start from `haar_sd.c` on branch
`origin/claude/selfdual-haar-d7-d8-rwwjp8` (`research/selfdual-hi/src/haar_sd.c`, README in that folder). Report
RANDORB and the family minimum. Seeds: 108601-108699.

## c6-hexagon: structured lifts of split Cayley hexagons (the table's own route, small structure first)

The table value is 30 copies of the incidence graph of H(7) (39,216 vertices each). The cell notes (§1-3b) and
`research/theorems/D8_COMPOUND.md` on branch `origin/claude/own-d8-compound-1z4e6s` show: H(q) + two perfect
matchings lifted over Z_10 gives 10 copies for free; annealed lifts are hopeless at q = 7; a Plücker pencil design
gave 13 copies at q = 5 (table: 25 at q = 5). Tools: `research/d10D8/hex/` (hexgen2 builds H(q), lift3 annealer,
hexcheck). Goal: find a voltage design (cyclic or small group, voltages on hexagon edges and matchings, given by a
formula) that reaches MORE copies than known at small q (q = 3, 4, 5) and that is defined for every q. Then build it
at q = 7 (≥ 31 copies, Δ = 10) or q = 8 with one matching (Δ = 10, ≥ 16 copies), and check it. Report, per q, the
largest number of copies you reach with zero far pairs. Seeds: 108701-108799.

## c7-throughput: more good descents per CPU-hour

The grind's only lever is how many low-energy chain minima it draws per CPU-hour (P(cost 0) per descent ≈ 1e-4).
Find a schedule that draws more: e.g. early abort (kill a chain whose cost at time t is above a threshold,
measured from data), shorter or longer COOL/REHEAT, start from the better of several random sets (RANDORB-style
pre-selection), ORBW=2/3/4, THREADS=1 vs batching. haar_sym2 prints CHAIN lines with min and secs; you may add
progress output to a copy of the code. Measure on psl 23 97 at equal CPU time against the reference F15W3: rate of
chain minima ≤ 12 and ≤ 9 per CPU-hour (run at least 30 min per variant; say how many descents). Seeds: 108801-108899.

## c8-wild: an approach none of the other cards uses

Other cards: c1 grind (F15W3 on psl 23 97 and prod), c2 two-orbit repair of known good states, c3 twisted cyclic
factor groups (tpgl, csl), c4 screen of direct-product groups, c5 twisted self-dual pairing S⁻¹ = β(S),
c6 hexagon lifts, c7 schedule throughput. Known dead (do not repeat): plain random S, inverse-closed S with e,
crossovers of good states, exhaustive best response, replica exchange, Frobenius (field-automorphism) orbits, single
orbits, Heisenberg groups, k = 5 on groups with large cyclic factors, z-only polishing (cell notes §4-§8,
`research/structured/STRUCTURE.md`). Pick ONE idea that changes the odds (another construction, another symmetry,
a non-Haar graph with a big automorphism group and a cheap exact check, a different cost function or move set),
write it down in NOTES.md with the reason it could work, build a fast exact scorer for it, and test it. If it dies
within 40 minutes, write why and try a second idea. Seeds: 108901-108999.

---

## Relaunches (round 1b)

### c3b-sl23x49: descents on SL(2,23) × Z49, the group c3 found (relaunch of slot c3, 21:56 UTC)

c3-twist found (c3-twist/NOTES.md, read it first): tpgl is worse; csl q with n ≡ 2 mod 4 is just SL(2,q) × Z_{n/2};
and `sl 23 49` (N = 595,056, 2N = 1,190,112, μ ≈ 70.5) has RANDORB min 47, p1 58, median 132, i.e. as good as
psl 23 97 (min 36, median 135) although its μ is 11 % larger. Only 6 F15W3 descents were run (minima 18-27).
Job: (1) run F15W3 descents on `sl 23 49` (one process, nice -n 10) for at least 60 minutes and compare the chain-minimum
distribution with psl 23 97 (median 18-21, 1 in 15 ≤ 9; c1-grind's g1.log is a live reference); (2) try ORBW=2 and
ORBW=4 for 20 minutes each; (3) RANDORB=1000 on other SL(2,q) × Z_n in the window that c4 is not covering
(check c4-groups/NOTES.md first; e.g. sl 13 271, sl 19 ... with every prime of n ≡ 1 mod 3). Report each group's
numbers in NOTES.md and a scoreboard line per new best. Seeds: 108451-108499.

### c8b-coset: anneal bipartite coset graphs over PSL(2,181) with stabilizer C5 (relaunch of slot c8, 22:06 UTC)

c8-wild (read c8-wild/NOTES.md and its coset.c / coset2.c first) built bipartite coset graphs X(G, H, HgH) with
G = PSL(2,181), |H| = 5, N = |G|/5 = 592,956 per side (2N = 1,185,912 > 1,176,480), degree 10 from two double
cosets of size 5 (the "h = 5, two double cosets" family, about 7e9 members). Uncovered vertices from a root come in
H-orbits of size 5, like k = 5 orbits, without a big cyclic factor. 60 random members: min 57, median 238 (about 11-48
units of 5; Haar k = 3 random sets on psl 23 97: 12-45 units of 3). Its cost takes 0.9 s per BFS, too slow to search.
Job: (1) make the exact cost at least 20× faster (ideas: bitset BFS over cosets of a cyclic subgroup like
haar_sym2 does, precomputed neighbour tables as uint32 arrays, early exit when the cost exceeds the current best,
BFS from the root to depth 7 only on the opposite side); check the fast cost against coset.c on 20 members; (2)
anneal on the family (move = replace one of the two double-coset representatives; F15W3-style restarts) and compare
the distribution of descent minima in units with Haar k = 3 descents (median 6-7 units, best 1 unit); (3) report.
A cost-0 member is a 1,185,912-vertex graph of diameter 8: save its definition in records/ and say so on the
scoreboard (CLAIM); the coordinator checks it with two independent BFS codes. Seeds: 108951-108999.

### c5b-cosetscreen: which coset-graph family is best? (relaunch of slot c5, 22:17 UTC)

Context: c8-wild/NOTES.md. Bipartite coset graphs X(G, H, D1 ∪ D2 ∪ ...) (vertices = left cosets of H on two
sides, adjacency by double cosets D_i = H g_i H; degree = Σ |D_i|/|H|) have the group G acting on each side with
stabilizer H, so a root's uncovered set is a union of H-orbits: with |H| = h it behaves like h-fold orbit symmetry
(μ_A ≈ μ/h, μ = N·exp(−5,380,840/N), N = |G|/h ≥ 588,241). c8 measured PSL(2,181), h = 5, two double cosets of size 5:
60 random members, min 57, median 238 (tax about 3.5× over μ). c8b-coset is building a fast evaluator and annealer
for that family; do NOT duplicate it. Your job is the SCREEN, to give c8b better targets: list (G, H, double-coset
type) with N in 588,241-610,000, e.g. PSL(2,181) h = 5 (N 592,956), PSL(2,193) h = 6 (C6 or S3, N 599,072),
PSL(2,229) h = 10 (C10 or D5, N 600,438), PGL(2,181) h = 10 (N 592,956), SL(2,q)/PGL(2,q) options, h = 4, 8, 12
(check orders yourself; a family needs at least about 10^8 members to be worth annealing). For each, sample 50-100
random members with c8's code (copy it; about 1 s per member is fine for a screen) and record μ, μ/h, family size, min /
median uncovered in units of h, and tax = median/μ. Also check connectedness (the D_i must generate G). Write a ranked
table in NOTES.md and one scoreboard line per family (cost = best uncovered, plain units). Seeds: 108651-108699.

### c6b-exhaust: scan two whole one-double-coset families (relaunch of slot c6, 23:40 UTC)

Read c5b-cosetscreen/NOTES.md (screen) and c8b-coset/NOTES.md + fastc.c (fast coset BFS, about 85 ms per member).
Two families with h = 10 and ONE regular double coset (degree 10) are small enough to enumerate completely:
- C: G = PGL(2,181), H = D5 (non-square reflection), N = 592,956 (2N = 1,185,912); about 59,000 members
  (c5b: 100 random, min 127, median 456; c8: 260 random, min 84);
- K: G = PSL(2,229), H = D5 in the non-split torus, N = 600,438 (2N = 1,200,876); about 60,000 members
  (c5b: 60 random, min 87, median 340).
Job: copy fastc.c into your folder, adapt it to these groups / subgroups (one double coset H g H with
|H ∩ g H g⁻¹| = 1), check it against c5b's code on 10 members of each family, reduce the enumeration by the normaliser
of H if you can (members g and n g n'... that give isomorphic graphs), then scan EVERY member of K and of C (one
process at a time, nice -n 10, checkpoint progress to a file every few minutes so a restart can resume). Report the
full distribution (min, p0.1, p1, median) and the 10 best members. A cost-0 member is a diameter-8 graph with more
than 1,176,480 vertices: save its definition in records/ and add a CLAIM line. Seeds (if any): 108751-108799.

### c1b-structure: what makes a good orbit set? (relaunch of slot c1, 23:48 UTC; light CPU)

c1-grind's two runs (g1, g2 in c1-grind/) stay alive until about 04:25; do not touch them, but read their logs.
Data: about 120 good states (energy 3-9) in shared/good_states.tsv, the CHAIN lines of c1-grind/g1.log, g2.log,
c7-throughput/*.log (one new energy-3 state), c3b-sl23x49/*.log, c4-groups/*.log, plus random orbit sets that you
generate. Question: is there a cheap statistic of S (computable in well under a second) that separates the sets
whose descents end low from random ones? Candidates: the duplicate-word rate and Z-coefficient structure (cell notes
§5, haar_zopt ZONLYDUP), the conjugacy classes / element orders of the orbit representatives' Q-parts, the number of
uncovered α-fixed elements, coverage of short words (|S⁻¹S|, |S S⁻¹ S| distinct counts), the "ball sizes" at radius
3 and 5. Measure them on the good states vs. random sets vs. the median chain end. If one separates them, test a
biased start (draw 50 random sets, start the descent from the best by your statistic) against the reference with a
step-based schedule (VCLOCK/MAXSTEPS in haar_sym2, so machine load does not bias the comparison), ≥ 60 chains each.
One light process at a time (nice -n 10). Seeds: 108151-108199.

### c8c-smooth: a smoother objective for the k = 3 annealer (relaunch of slot c8, 00:08 UTC)

c8/c8b/c5b: coset graphs are about 3× worse than Haar k = 3 orbits (c8b-coset/NOTES.md), so back to Haar. The
annealer's energy is the uncovered count only: almost every move changes it by a lot and good states are isolated
(cell notes §6, §8.3). Idea: add a small secondary term that measures how FRAGILE the coverage is, so the descent can
tell apart sets with equal uncovered counts. The BFS gives one for free: F = number of B-side elements first reached
at the last level (radius 7) = N − |B-side ball of radius 5| − uncovered (the more elements depend on the last level,
the more fragile). Energy' = energy + w·F/1000 with w small (try w = 0.5, 1, 2), or F only as a tie-breaker. Job:
copy research/d10D8/sym2/haar_sym2.c into your folder, add the term (env SMOOTHW=w; keep the reported "cost" and the
CHAIN min as the TRUE energy, and keep its own full check before writing a solution), check on 5 sets that the true
cost is unchanged, then compare on psl 23 97 with a STEP-based schedule (VCLOCK/MAXSTEPS, so machine load does not
bias it) against the unmodified code: ≥ 60 chains each, distribution of chain minima (≤ 12, ≤ 9, median). One heavy
process at a time, nice -n 10. Seeds: 108961-108999.

### c5c-scanC: full scan of coset family C (relaunch of slot c5, 00:30 UTC)

c6b-exhaust (read c6b-exhaust/NOTES.md and exh.c, run_all.sh, summ.py) reduced the two one-double-coset families to
about 16,000 classes each and validated its BFS against c5b. c6b now scans family K only. You scan family C:
G = PGL(2,181), H = D5 (non-square reflection), N = 592,956 (2N = 1,185,912). Copy exh.c / run_all.sh / summ.py
into your folder (do not write in c6b's folder), run the A-root pass over every C class (resumable, nohup, nice -n 10,
one process), then the B-root pass only for classes whose A-root part (uBA + uAA) is at most 50, best first.
Report the full distribution and the 10 best classes in NOTES.md and the scoreboard. A class with full cost 0 is a
diameter-8 graph on 1,185,912 vertices: save its definition in records/ and add a CLAIM line. Seeds: 108601-108649.

### c7b-design: read the structure out of the annealed hexagon lifts (relaunch of slot c7, 00:50 UTC; light CPU)

c6-hexagon (read c6-hexagon/NOTES.md and src/) found VALID lifts of H(q) + two perfect matchings over cyclic groups
by annealing: q = 3 over Z24 (beats the table's 20 copies at Δ6), q = 4 over Z20 (= 20), q = 5 over Z15 and Z14
(the table has 25 at Δ8; the lab's formula design had 13). The table's (10,8) graph is 30 copies of H(7) (Δ = q+3);
annealing cannot reach q = 7 (one evaluation about a minute, and random voltages need far too many to line up).
Job: look for STRUCTURE in the valid voltage assignments (they are in c6's files): voltage distributions on hexagon
edges vs matching edges, dependence on point/line coordinates of H(q) (hexgen2 builds H(q) from coordinates), whether
voltages can be normalised (switching at vertices: adding f(v) to every dart out of v keeps the lift isomorphic) to
something with few distinct values, symmetry under the automorphisms of H(q). Then propose a formula family
(voltages given by a short rule in the coordinates, with a few parameters), test it at q = 3, 4, 5 with c6's checker
(src/hexeval.c, 0.6 s per evaluation at q = 5, one process, nice -n 10), and, if it reproduces valid lifts, build it
at q = 7 with 31 copies (Δ = 10, 1,215,696 vertices) and check. Write what you find in NOTES.md, positive or negative.
Seeds: 108851-108899.

### c2b-digest: keep a running digest of the squad for the coordinator (relaunch of slot c2, 00:50 UTC; no CPU)

Every 25-30 minutes until about 03:30 UTC, rewrite research/squads/handsoff-108/DIGEST.md: one table row per
worker folder (c1-grind ... c8c-smooth, including finished ones): card, status (running / done, and whether its
processes are alive), the key numbers (best cost in its units, sample sizes, comparisons with the reference), the main
finding in one sentence, and anything that looks like a claim of cost 0 (flag it at the top in bold). Below the table,
keep a short list "Leads worth more CPU" and "Dead ends", each with the evidence (file + numbers). Sources: each
folder's NOTES.md, scoreboard.tsv, log tails (tail/grep only, never print big files). Be exact; copy numbers, do not
round them into new claims. Do not run any search yourself. Poll with sleep loops of under 10 minutes per Bash call;
do not end your turn until 03:30 UTC.

### c6c-h12: one-regular-double-coset families with h = 12 in PGL(2,193) (relaunch of slot c6, 01:00 UTC)

c6b-exhaust scanned ALL 16,293 classes of family K (PSL(2,229), H = D5, one regular double coset, h = 10): best exact
cost 4 (class 4233), p0.1 54, median 338: close, but no cost 0 (c6b-exhaust/NOTES.md). c5c-scanC is scanning family
C (PGL(2,181), H = D5). The next size up: G = PGL(2,193) (order 7,188,864), |H| = 12, N = 599,072 (2N = 1,198,144),
μ ≈ 75, μ/h ≈ 6.2 (K: 7.7). Candidate H of order 12: C12 (in the split torus; 193 ≡ 1 mod 12), D6 (both kinds of
reflections: square and non-square determinant), A4. Degree 10 needs ONE regular double coset (|H ∩ gHg⁻¹| = 1 gives
12 neighbours, too many) — so check what double-coset sizes exist: |HgH|/|H| = 12/|H ∩ gHg⁻¹| ∈ {12, 6, 4, 3, 2, 1}.
Degree 10 = e.g. 6 + 4, 6 + 3 + 1, 4 + 4 + 2, ... (c5b found families with non-regular double cosets 3-10× worse, but
check the smallest-k types here). Job: copy c6b's exh.c (it already does PGL(2,q) for prime q, classes under the
normaliser and inversion, A-root and B-root passes), adapt to these H and types, check connectivity, sample 100
members per family (min / median in units of 12, compare with K's 338/10 per unit), then fully scan the best family
(A-root pass on all classes, B-root on those with A-part ≤ 50). One process at a time, nice -n 10, resumable. A full
cost 0 is a diameter-8 graph on 1,198,144 vertices: records/ + CLAIM line. Seeds: 108701-108749.

### c3c-grind: one more F15W3 grind on psl 23 97 until 03:25 UTC (relaunch of slot c3, 01:40 UTC)

All structural cards so far lost to the plain k = 3 grind on psl 23 × Z97 (DIGEST.md). Run one more fresh-seed F15W3
process on `psl 23 97` (seed 108471, then 108472... on restart; nice -n 12, THREADS=1, timeout so it ends by 03:25 UTC,
log in your folder), exactly as c1-grind's g1 (read c1-grind/NOTES.md for the command). Every 10-15 minutes: count
CHAIN lines and minima, update NOTES.md; any chain at energy ≤ 6 gets a scoreboard line; any chain at energy ≤ 3:
run EXDESC=1 on its set (CKPT file with that set; see research/d10D8/README.md) in your folder. If the run reaches
cost 0: copy the solution to records/, run shared/check.sh on it, CLAIM line. At 03:25 UTC stop your process, write
the final counts (chains, min, median, ≤ 12, ≤ 9) in NOTES.md and reply. Seeds: 108471-108480.

### c8d-grind: second extra F15W3 grind on psl 23 97 until 03:25 UTC (relaunch of slot c8, 02:18 UTC)

Same as c3c-grind (read that card), with seeds 108981-108990, your own folder c8d-grind/, nice -n 12, stop at 03:25 UTC.
